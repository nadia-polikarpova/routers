use egg::{rewrite as rw, *};
use std::iter::{once, repeat};

use crate::named::{var_symbol, Lambda, COMPOSE_20_ID, COMPOSE_20_LAM};
use fxhash::FxHashMap as HashMap;
use fxhash::FxHashSet as HashSet;

#[derive(Debug, PartialEq, Clone)]
pub enum Router {
    C, // left
    B, // right
    S, // both
}

impl Router {
    // Does this router route the left child?
    pub fn routes_left(&self) -> bool {
        match self {
            Router::C => true,
            Router::B => false,
            Router::S => true,
        }
    }

    // Does this router route the right child?
    pub fn routes_right(&self) -> bool {
        match self {
            Router::C => false,
            Router::B => true,
            Router::S => true,
        }
    }
}

type Routers = Vec<Router>;

define_language! {
    /// A language if CBSI combinators from
    /// Liang, Jordan, Klein. "Learning Programs: A Hierarchical Bayesian Approach. ICML 2010"
    pub enum Comb {
        Num(i32),
        "I" = I, // identity
        "$" = App([Id; 3]), // first child is a list of routers represented as symbol (use "." for empty list)
        Symbol(egg::Symbol),
        Add(i32), // partially applied plus, used during constant folding
    }
}

impl Comb {
    pub fn is_plus(&self) -> bool {
        match self {
            Comb::Symbol(s) => s == &egg::Symbol::from("+"),
            _ => false,
        }
    }

    pub fn get_routers(&self) -> Option<Routers> {
        match self {
            Comb::Symbol(s) => {
                let mut routers = vec![];
                for c in s.to_string().chars() {
                    match c {
                        'C' => routers.push(Router::C),
                        'B' => routers.push(Router::B),
                        'S' => routers.push(Router::S),
                        '.' => (),
                        _ => return None,
                    }
                }
                Some(routers)
            }
            _ => None,
        }
    }

    // TODO: change to take an iterator?
    pub fn make_routers(routers: &[Router]) -> Self {
        let mut s = String::new();
        if routers.is_empty() {
            s.push('.');
        }
        for router in routers {
            match router {
                Router::C => s.push('C'),
                Router::B => s.push('B'),
                Router::S => s.push('S'),
            }
        }

        Comb::Symbol(egg::Symbol::from(s))
    }
}

/// Partition a list of variables into a left and right lists accoridng to the routers
fn route_vars(vars: &[egg::Symbol], routers: &[Router]) -> (Vec<egg::Symbol>, Vec<egg::Symbol>) {
    assert!(routers.len() >= vars.len()); // all variables must be routed
    let mut left_vars = vec![];
    let mut right_vars = vec![];
    for (router, var) in routers.iter().zip(vars.iter()) {
        match router {
            Router::C => {
                left_vars.push(*var);
            }
            Router::B => {
                right_vars.push(*var);
            }
            Router::S => {
                left_vars.push(*var);
                right_vars.push(*var);
            }
        }
    }
    (left_vars, right_vars)
}

/// Convert a lambda expression into a combinator expression
pub fn from_lambda_expr(expr: &RecExpr<Lambda>) -> RecExpr<Comb> {
    // Recursive pass: compute list of free variables for every node
    let mut free_vars: Vec<Vec<egg::Symbol>> = vec![vec![]; expr.as_ref().len()];
    let mut var_set = HashSet::default();
    compute_free_vars(
        expr,
        Id::from(expr.as_ref().len() - 1),
        &mut free_vars,
        &mut var_set,
        &vec![],
    );

    // Linear pass: gradually add nodes to the combinator expression
    // - replacing variables with I
    // - skipping lambdas
    // - inserting appropriate routers at each application based on the free variables of the children
    // - translating lets into applications
    let mut res = RecExpr::default();
    let mut mapping = HashMap::default(); // maps from lambda node id to combinator node id
    for (id, node) in expr.as_ref().iter().enumerate() {
        let new_id = match node {
            Lambda::Num(n) => res.add(Comb::Num(*n)),
            Lambda::Symbol(s) => {
                if var_set.contains(s) {
                    // This is a variable, no need to add (we assume variables and built-in symbols don't overlap)
                    Id::from(0)
                } else {
                    res.add(Comb::Symbol(*s))
                }
            }
            Lambda::Var(_) => res.add(Comb::I),
            Lambda::Lambda([_, body]) => mapping[&usize::from(*body)], // skip lambdas, but map them to the translation of their body, in case they are referenced by some application or let
            Lambda::App([l, r]) => add_application(
                &mut res,
                id,
                usize::from(*l),
                usize::from(*r),
                &free_vars,
                &mapping,
            ),
            Lambda::Let([_, value, body]) => add_application(
                &mut res,
                id,
                usize::from(*body),
                usize::from(*value),
                &free_vars,
                &mapping,
            ),
            Lambda::Add(_) => unreachable!("Add cannot occur in surface language"),
        };
        mapping.insert(id, new_id);
    }

    res
}

/// Helper function for converting a lambda expression into a combinator expression:
/// recursively process `expr` at `id` to compute `free_vars`,
/// which maps each node to its free variables in the order in which they are bound.
/// `scoped_vars` is the list of variables that are already bound in the current context, passed top-down.
fn compute_free_vars(
    expr: &RecExpr<Lambda>,
    id: Id,
    free_vars: &mut Vec<Vec<egg::Symbol>>,
    var_set: &mut HashSet<egg::Symbol>,
    scope_vars: &Vec<egg::Symbol>,
) {
    let node = &expr[id];
    match node {
        Lambda::Var(var_id) => {
            let var_symbol = var_symbol(expr, *var_id);
            free_vars[usize::from(id)] = vec![var_symbol];
            var_set.insert(var_symbol);
        }
        Lambda::App([l, r]) => {
            compute_free_vars(expr, *l, free_vars, var_set, scope_vars);
            compute_free_vars(expr, *r, free_vars, var_set, scope_vars);
            free_vars[usize::from(id)] = scope_vars
                .iter()
                .filter(|v| {
                    free_vars[usize::from(*l)].contains(v) || free_vars[usize::from(*r)].contains(v)
                })
                .cloned()
                .collect();
        }
        Lambda::Lambda([var_id, body]) => {
            let new_var = var_symbol(expr, *var_id);
            let mut new_scope_vars = scope_vars.clone();
            new_scope_vars.push(new_var);
            compute_free_vars(expr, *body, free_vars, var_set, &new_scope_vars);
            let mut my_free_vars = free_vars[usize::from(*body)].clone();
            // Remove `new_var` from my free vars, which must be the last of my body's free vars
            if my_free_vars.last() == Some(&new_var) {
                my_free_vars.pop();
            }
            free_vars[usize::from(id)] = my_free_vars;
        }
        Lambda::Let([var_id, value, body]) => {
            compute_free_vars(expr, *value, free_vars, var_set, scope_vars);
            let new_var = var_symbol(expr, *var_id);
            let mut new_scope_vars = scope_vars.clone();
            new_scope_vars.push(new_var);
            compute_free_vars(expr, *body, free_vars, var_set, &new_scope_vars);
            free_vars[usize::from(id)] = scope_vars
                .iter()
                .filter(|v| {
                    free_vars[usize::from(*value)].contains(v)
                        || (free_vars[usize::from(*body)].contains(v) && **v != new_var)
                })
                .cloned()
                .collect();
        }
        _ => (),
    }
}

/// Helper function for converting a named lambda calculus expression into a combinator expression;
/// this function adds an application with appropriate routers
fn add_application(
    expr: &mut RecExpr<Comb>, // combinator expression under construction
    parent: usize,            // index of current application node in named expression
    left: usize,              // index of left child in named expression
    right: usize,             // index of right child in named expression
    free_vars: &Vec<Vec<egg::Symbol>>, // free variables of each node in named expression, in the order of binding
    mapping: &HashMap<usize, Id>, // mapping from named expression indices to combinator expression indices
) -> Id {
    let vars = &free_vars[parent];
    // compute the router for each variable based on which children contain it free:
    let mut routers = vec![];
    for var_id in vars {
        let left_contains = free_vars[left].contains(var_id);
        let right_contains = free_vars[right].contains(var_id);
        if left_contains && right_contains {
            routers.push(Router::S);
        } else if left_contains {
            routers.push(Router::C);
        } else if right_contains {
            routers.push(Router::B);
        }
    }

    // add the routers and then the application
    let r_id = expr.add(Comb::make_routers(&routers));
    expr.add(Comb::App([r_id, mapping[&left], mapping[&right]]))
}

/// Convert a combinator expression into a lambda expression
pub fn to_lambda_expr(expr: &RecExpr<Comb>) -> RecExpr<Lambda> {
    // First pass: compute a mapping from I-nodes to variables and from applications to variables they bind
    let mut var_mapping = HashMap::default();
    let mut total_vars = 0;
    compute_vars(
        expr,
        Id::from(expr.as_ref().len() - 1),
        &mut var_mapping,
        &mut total_vars,
        &vec![],
    );

    // Second pass: gradually add nodes to the lambda expression translating:
    // - I-nodes to variables according to var_mapping
    // - applications to either applications or lambdas, also according to var_mapping
    let mut res = RecExpr::default();
    let mut mapping = HashMap::default(); // maps from combinator node id to lambda node id
    for (id, node) in expr.as_ref().iter().enumerate() {
        let new_id = match node {
            Comb::Num(n) => res.add(Lambda::Num(*n)),
            Comb::Symbol(s) => res.add(Lambda::Symbol(*s)),
            Comb::I => {
                let vars = &var_mapping[&Id::from(id)];
                assert!(vars.len() == 1 || vars.len() == 0);
                if vars.len() == 1 {
                    // This is a variable:
                    let s_id = res.add(Lambda::Symbol(vars[0]));
                    res.add(Lambda::Var(s_id))
                } else {
                    // This is an identity function:
                    let s_id = res.add(Lambda::Symbol(egg::Symbol::from("x")));
                    let body_id = res.add(Lambda::Var(s_id));
                    res.add(Lambda::Lambda([s_id, body_id]))
                }
            }
            Comb::App([_, l, r]) => {
                let vars = &var_mapping[&Id::from(id)];
                let body_id = res.add(Lambda::App([mapping[l], mapping[r]]));
                // Create a lambda for each variable that is not bound here:
                let mut res_id = body_id;
                for var in vars.iter().rev() {
                    let s_id = res.add(Lambda::Symbol(*var));
                    res_id = res.add(Lambda::Lambda([s_id, res_id]));
                }
                res_id
            }
            Comb::Add(_) => unreachable!("Add cannot occur in surface language"),
        };
        mapping.insert(Id::from(id), new_id);
    }
    res
}

/// Helper function for converting a combinator expression into a lambda expression:
/// recursively process `expr` at `id` to compute `var_mapping`,
/// which maps each I-node to the variable it represents and each application to the variables it binds;
/// `total_vars` is the number of variables that have been bound so far and is used to generate fresh variable names;
/// `vars` is the list of variables that are already bound in the current context.
fn compute_vars(
    expr: &RecExpr<Comb>,
    id: Id,
    var_mapping: &mut HashMap<Id, Vec<egg::Symbol>>,
    total_vars: &mut usize,
    vars: &Vec<egg::Symbol>,
) {
    let node = &expr[id];
    match node {
        Comb::I => {
            assert!(vars.len() == 1 || vars.len() == 0); // I-nodes can represent either a variable or an identity function
            var_mapping.insert(id, vars.clone());
        }
        Comb::App([rts, l, r]) => {
            let routers = expr[*rts].get_routers().unwrap(); // first child of app is always a router node
            assert!(routers.len() >= vars.len()); // at least we have routers for all variables that are already bound!
            let mut new_vars = vec![]; // newly bound variables
            for _ in vars.len()..routers.len() {
                // create a new variable for every extra router
                let var = egg::Symbol::from(format!("x{}", total_vars));
                *total_vars += 1;
                new_vars.push(var);
            }
            let all_vars = [&vars[..], &new_vars[..]].concat();
            var_mapping.insert(id, new_vars); // remember which variables are bound here (if new_vars is empty, this node will be treated as application, and otherwise as lambda)
            let (l_vars, r_vars) = route_vars(&all_vars, &routers);
            compute_vars(expr, *l, var_mapping, total_vars, &l_vars);
            compute_vars(expr, *r, var_mapping, total_vars, &r_vars);
        }
        _ => (),
    }
}

/// Constant folding for combinator expressions
#[derive(Default)]
struct CombAnalysis;

#[derive(Debug)]
struct Data {
    constant: Option<Comb>,
    routers: Option<Routers>, // only defined for symbols that are routers
}

type EGraph = egg::EGraph<Comb, CombAnalysis>;

/// Constant folding: same implementation as for lambda expressions
fn eval(egraph: &EGraph, enode: &Comb) -> Option<Comb> {
    let x = |i: &Id| egraph[*i].data.constant.as_ref();
    match enode {
        Comb::Num(_) => Some(enode.clone()),
        _ if enode.is_plus() => Some(enode.clone()),
        Comb::App([_, l, r]) => match (x(l)?, x(r)?) {
            (l_const, Comb::Num(n)) if l_const.is_plus() => Some(Comb::Add(*n)),
            (Comb::Add(n), Comb::Num(m)) => Some(Comb::Num(n + m)),
            _ => None,
        },
        _ => None,
    }
}

impl Analysis<Comb> for CombAnalysis {
    type Data = Data;
    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        assert_eq!(to.routers, from.routers, "routers should be the same");
        if to.constant.is_none() && from.constant.is_some() {
            to.constant = from.constant;
            DidMerge(true, false)
        } else {
            DidMerge(false, true)
        }
    }

    fn make(egraph: &EGraph, enode: &Comb) -> Data {
        Data {
            constant: eval(egraph, enode),
            routers: enode.get_routers(),
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant.clone() {
            let const_id = egraph.add(c);
            egraph.union(id, const_id);
        }
    }
}

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

/// Do none of the routers in the e-class matched by `rts` pointing to the left (i.e. they are all B)?
/// This condition assumes that `rts` could only match a router e-class.
fn no_lefts(rts: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        egraph[subst[rts]]
            .data
            .routers
            .as_ref()
            .unwrap()
            .iter()
            .all(|r| !r.routes_left())
    }
}

fn ends_with_b(rts: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        egraph[subst[rts]]
            .data
            .routers
            .as_ref()
            .unwrap()
            .iter()
            .last()
            .map(|r| r == &Router::B)
            .unwrap_or(false)
    }
}

/// Is an application whose parent's routers are `parent_rts` and whose left child's routers are `child_rts` a beta-redex?
/// Yes if the child has more routers than parent has pointing to the left.
fn is_redex(parent_rts: Var, child_rts: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| {
        let n_parent_routers = egraph[subst[parent_rts]]
            .data
            .routers
            .as_ref()
            .unwrap()
            .iter()
            .filter(|r| r.routes_left())
            .count();
        let n_child_routers = egraph[subst[child_rts]]
            .data
            .routers
            .as_ref()
            .unwrap()
            .iter()
            .count();
        n_child_routers > n_parent_routers
    }
}

fn rules() -> Vec<Rewrite<Comb, CombAnalysis>> {
    vec![
        rw!("add-assoc-0"; "($ . ($ . + ($ . ($ . + ?a) ?b)) ?c)" => "($ . ($ . + ?a) ($ . ($ . + ?b) ?c))"),
        rw!("add-assoc-1"; "($ C ($ B + ($ C ($ B + ?a) ?b)) ?c)" =>
                           "($ C ($ B + ?a) ($ . ($ . + ?b) ?c))"),
        rw!("id"; "($ ?r I ?x)" => "?x" if no_lefts(var("?r"))),
        // rw!("eta"; "($ ?r ?x I)" => "?x" if ends_with_b(var("?r"))),
        rw!("beta";
        "($ ?r0 ($ ?rl ?x ?y) ?z)" =>
        { Beta {
            r0: var("?r0"),
            rl: var("?rl"),
            x: var("?x"),
            y: var("?y"),
            rp_new: var("?rp_new"),
            r1_new: var("?r1_new"),
            r2_new: var("?r2_new"),
            x_new: var("?x_new"),
            y_new: var("?y_new"),
            beta_b: "($ ?rp_new ?x ($ ?r2_new ?y_new ?z))".parse().unwrap(),
            beta_c: "($ ?rp_new ($ ?r1_new ?x_new ?z) ?y)".parse().unwrap(),
            beta_s: "($ ?rp_new ($ ?r1_new ?x_new ?z) ($ ?r2_new ?y_new ?z))".parse().unwrap(),
        }} if is_redex(var("?r0"), var("?rl"))),
    ]
}

struct Beta {
    r0: Var,
    rl: Var,
    x: Var,
    y: Var,
    rp_new: Var,
    r1_new: Var,
    r2_new: Var,
    x_new: Var,
    y_new: Var,
    beta_b: Pattern<Comb>,
    beta_c: Pattern<Comb>,
    beta_s: Pattern<Comb>,
}

impl Applier<Comb, CombAnalysis> for Beta {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Comb>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        // The names of various sequences of routers (r0, r1, etc) correspond to those used in Fig 5 in the paper.
        let r0 = egraph[subst[self.r0]].data.routers.as_ref().unwrap();
        let split_point = r0.iter().filter(|r| r.routes_left()).count();
        // split rl into r1 and r at the split point:
        let rl = egraph[subst[self.rl]].data.routers.as_ref().unwrap();
        if rl.len() <= split_point {
            return vec![]; // not a redex
        }
        // let input_pat: Pattern<Comb> = "($ ?r0 ($ ?rl ?x ?y) ?z)".parse().unwrap();
        // let before_term = show_match(egraph, subst, &input_pat);
        let (r1, r) = rl.split_at(split_point);
        assert!(!r.is_empty()); // enforced by the condition `is_redex`
        let (core, r) = (r[0].clone(), &r[1..]); // split off the core router
        let (mut rp_new, r1_new, r2_new, pat) = self.new_routers(&core, r0, r1, r);
        rp_new.extend(r.iter().cloned()); // r is always added to the end of the parent routers
        assert!(r0.len() <= rp_new.len());

        let mut subst = subst.clone();
        let rp_new_sym = Comb::make_routers(&rp_new);
        subst.insert(self.rp_new, egraph.add(rp_new_sym));
        if let Some((r1_new, m1)) = r1_new {
            // if r1_new.len() > m1 {
            //     return vec![]; // adapter needed
            // }
            let r1_new_sym = Comb::make_routers(&r1_new);
            subst.insert(self.r1_new, egraph.add(r1_new_sym));
            let adapter_id = Beta::add_adapter(egraph, subst[self.x], m1, r1_new.len() - m1);
            subst.insert(self.x_new, adapter_id);
        }
        if let Some((r2_new, m2)) = r2_new {
            if r2_new.len() > m2 {
                return vec![]; // inserting adapters in this position causes the e-graphs to grow infinitely; I don't really understand why
            }
            let r2_new_sym = Comb::make_routers(&r2_new);
            subst.insert(self.r2_new, egraph.add(r2_new_sym));
            let adapter_id = Beta::add_adapter(egraph, subst[self.y], m2, r2_new.len() - m2);
            subst.insert(self.y_new, adapter_id);
        }
        let ids = pat.apply_one(egraph, eclass, &subst, searcher_ast, rule_name);
        // if !ids.is_empty() {
        //     // println!("BEFORE: {}", to_lambda_expr(&before_term.parse().unwrap()));
        //     // println!("AFTER: {}", to_lambda_expr(&show_match(egraph, &subst, pat).parse().unwrap()));
        //     println!("BEFORE: {}", before_term);
        //     println!("AFTER: {}", show_match(egraph, &subst, pat));
        // }
        ids
    }
}

impl Beta {
    fn new_routers(
        &self,
        core: &Router,
        r0: &[Router],
        r1: &[Router],
        r: &[Router],
    ) -> (
        Vec<Router>,
        Option<(Vec<Router>, usize)>,
        Option<(Vec<Router>, usize)>,
        &Pattern<Comb>,
    ) {
        match core {
            Router::B => self.new_routers_b(r0, r1, r),
            Router::C => self.new_routers_c(r0, r1, r),
            Router::S => self.new_routers_s(r0, r1, r),
        }
    }

    fn new_routers_b(
        &self,
        r0: &[Router],
        r1: &[Router],
        r: &[Router],
    ) -> (
        Vec<Router>,
        Option<(Vec<Router>, usize)>,
        Option<(Vec<Router>, usize)>,
        &Pattern<Comb>,
    ) {
        let mut r0_new = vec![];
        let mut r2_new = vec![];
        let mut r1_idx = 0;
        for router in r0 {
            match router {
                Router::B => {
                    // routes to z (now B -> B)
                    r0_new.push(Router::B);
                    r2_new.push(Router::B);
                }
                Router::C => {
                    match r1[r1_idx] {
                        Router::B => {
                            // routes to y (now B -> C)
                            r0_new.push(Router::B);
                            r2_new.push(Router::C);
                        }
                        Router::C => {
                            // routes to x (now C)
                            r0_new.push(Router::C);
                        }
                        Router::S => {
                            // routes to x and y
                            r0_new.push(Router::S);
                            r2_new.push(Router::C);
                        }
                    }
                }
                Router::S => {
                    match r1[r1_idx] {
                        Router::B => {
                            // routes to y and z
                            r0_new.push(Router::B);
                            r2_new.push(Router::S);
                        }
                        Router::C => {
                            // routes to x and z
                            r0_new.push(Router::S);
                            r2_new.push(Router::B);
                        }
                        Router::S => {
                            // routes to x, y, and z
                            r0_new.push(Router::S);
                            r2_new.push(Router::S);
                        }
                    }
                }
            }
            if router.routes_left() {
                r1_idx += 1;
            }
        }
        let m2 = r2_new.len();
        // Now for every router in r that routes right (to y), we need to add a router to r2_new that routes left (to y)
        for router in r {
            if router.routes_right() {
                r2_new.push(Router::C);
            }
        }
        (r0_new, None, Some((r2_new, m2)), &self.beta_b)
    }

    fn new_routers_c(
        &self,
        r0: &[Router],
        r1: &[Router],
        r: &[Router],
    ) -> (
        Vec<Router>,
        Option<(Vec<Router>, usize)>,
        Option<(Vec<Router>, usize)>,
        &Pattern<Comb>,
    ) {
        let mut r0_new = vec![];
        let mut r1_new = vec![];
        let mut r1_idx = 0;
        for router in r0 {
            match router {
                Router::B => {
                    // routes to z (now C -> B)
                    r0_new.push(Router::C);
                    r1_new.push(Router::B);
                }
                Router::C => {
                    match r1[r1_idx] {
                        Router::B => {
                            // routes to y (now B)
                            r0_new.push(Router::B);
                        }
                        Router::C => {
                            // routes to x (now C -> C)
                            r0_new.push(Router::C);
                            r1_new.push(Router::C);
                        }
                        Router::S => {
                            // routes to x and y
                            r0_new.push(Router::S);
                            r1_new.push(Router::C);
                        }
                    }
                }
                Router::S => {
                    match r1[r1_idx] {
                        Router::B => {
                            // routes to y and z
                            r0_new.push(Router::S);
                            r1_new.push(Router::B);
                        }
                        Router::C => {
                            // routes to x and z
                            r0_new.push(Router::C);
                            r1_new.push(Router::S);
                        }
                        Router::S => {
                            // routes to x, y, and z
                            r0_new.push(Router::S);
                            r1_new.push(Router::S);
                        }
                    }
                }
            }
            if router.routes_left() {
                r1_idx += 1;
            }
        }
        let m1 = r1_new.len();
        // For each router in r that routes left (to x), we need to add a new router to r1_new that will also route left to x.
        for router in r {
            if router.routes_left() {
                r1_new.push(Router::C);
            }
        }

        (r0_new, Some((r1_new, m1)), None, &self.beta_c)
    }

    fn new_routers_s(
        &self,
        r0: &[Router],
        r1: &[Router],
        r: &[Router],
    ) -> (
        Vec<Router>,
        Option<(Vec<Router>, usize)>,
        Option<(Vec<Router>, usize)>,
        &Pattern<Comb>,
    ) {
        let mut r0_new = vec![];
        let mut r1_new = vec![];
        let mut r2_new = vec![];
        let mut r1_idx = 0;
        for router in r0 {
            match router {
                Router::B => {
                    // routes to z (now B -> B and C -> B)
                    r0_new.push(Router::S);
                    r1_new.push(Router::B);
                    r2_new.push(Router::B);
                }
                Router::C => {
                    match r1[r1_idx] {
                        Router::B => {
                            // routes to y (now B -> C)
                            r0_new.push(Router::B);
                            r2_new.push(Router::C);
                        }
                        Router::C => {
                            // routes to x (now C -> C)
                            r0_new.push(Router::C);
                            r1_new.push(Router::C);
                        }
                        Router::S => {
                            // routes to x and y
                            r0_new.push(Router::S);
                            r1_new.push(Router::C);
                            r2_new.push(Router::C);
                        }
                    }
                }
                Router::S => {
                    match r1[r1_idx] {
                        Router::B => {
                            // routes to y and z
                            r0_new.push(Router::S);
                            r1_new.push(Router::B);
                            r2_new.push(Router::S);
                        }
                        Router::C => {
                            // routes to x and z
                            r0_new.push(Router::S);
                            r1_new.push(Router::S);
                            r2_new.push(Router::B);
                        }
                        Router::S => {
                            // routes to x, y, and z
                            r0_new.push(Router::S);
                            r1_new.push(Router::S);
                            r2_new.push(Router::S);
                        }
                    }
                }
            }
            if router.routes_left() {
                r1_idx += 1;
            }
        }
        let (m1, m2) = (r1_new.len(), r2_new.len());
        // For any router in r that routes left (to x), we need to add a new router to r1_new that will also route left to x,
        // and for any router in r that routes right (to y), we need to add a new router to r2_new that will also route to y (now left).
        for router in r {
            if router.routes_left() {
                r1_new.push(Router::C);
            }
            if router.routes_right() {
                r2_new.push(Router::C);
            }
        }
        (r0_new, Some((r1_new, m1)), Some((r2_new, m2)), &self.beta_s)
    }

    pub fn add_adapter(egraph: &mut EGraph, adaptee: Id, m: usize, n: usize) -> Id {
        let mut cur_id = adaptee;
        let i_id = egraph.add(Comb::I);
        for i in m..m + n {
            // Create a router with `i` Cs, a B, and a C:
            let routers = Comb::make_routers(
                &repeat(Router::C)
                    .take(i)
                    .chain(once(Router::B))
                    .chain(once(Router::C))
                    .collect::<Vec<_>>(),
            );
            let s_id = egraph.add(routers);
            // Create an application of the previous node to I with routers
            cur_id = egraph.add(Comb::App([s_id, cur_id, i_id]));
        }
        cur_id
    }
}

fn show_match(egraph: &EGraph, subst: &Subst, pattern: &Pattern<Comb>) -> String {
    let extractor = Extractor::new(&egraph, AstSize);
    let mut res = format!("{}", pattern);
    for var in pattern.vars() {
        let expr = extractor.find_best(subst[var]).1;
        res = res.replace(&format!("{}", var), &format!("{}", expr));
    }
    res
}

///////// Tests ///////////

static COMPOSE_20_COMB: &str = "($ . ($ C
        ($ SS ($ CB I I)
            ($ SS ($ CB I I)
                ($ SS ($ CB I I)
                    ($ SS ($ CB I I)
                        ($ SS ($ CB I I)
                            ($ SS ($ CB I I)
                                ($ SS ($ CB I I)
                                    ($ SS ($ CB I I)
                                        ($ SS ($ CB I I)
                                            ($ SS ($ CB I I)
                                                ($ SS ($ CB I I)
                                                    ($ SS ($ CB I I)
                                                        ($ SS ($ CB I I)
                                                            ($ SS ($ CB I I)
                                                                ($ SS ($ CB I I)
                                                                    ($ SS ($ CB I I)
                                                                        ($ SS ($ CB I I)
                                                                            ($ SS ($ CB I I)
                                                                            ($ CS ($ CB I I) I)))))))))))))))))))
            ($ C ($ B + I) 1))
            ($ CBB I ($ CB I I)))";

static COMPOSE_8_COMB: &str = "($ . ($ C 
        ($ SS ($ CB I I)
            ($ SS ($ CB I I)
                ($ SS ($ CB I I)
                    ($ SS ($ CB I I)
                        ($ SS ($ CB I I)
            ($ SS ($ CB I I) ($ CS ($ CB I I) I)))))))
        ($ C ($ B + I) 1))
        ($ CBB I ($ CB I I)))";

#[test]
pub fn conversion_inc() {
    let lambda_expr: RecExpr<Lambda> = "(lam y ($ ($ + (var y)) 1))".parse().unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    println!("{}", comb_expr.pretty(80));
    assert!(format!("{}", comb_expr) == "($ C ($ B + I) 1)");
}

#[test]
pub fn conversion_compose() {
    let lambda_expr: RecExpr<Lambda> = "(lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))"
        .parse()
        .unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    println!("{}", comb_expr.pretty(80));
    assert!(format!("{}", comb_expr) == "($ CBB I ($ CB I I))");
}

#[test]
pub fn conversion_let() {
    let lambda_expr: RecExpr<Lambda> = "(let x 1 (lam y ($ ($ + (var y)) (var x))))"
        .parse()
        .unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    println!("{}", comb_expr.pretty(80));
    assert!(format!("{}", comb_expr) == "($ . ($ BC ($ B + I) I) 1)");
}

#[test]
pub fn conversion_let_compose() {
    let lambda_expr: RecExpr<Lambda> =
        "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
                                        (let add1 (lam x ($ ($ + (var x)) 1))
                                        ($ ($ (var compose) (var add1)) (var add1))))"
            .parse()
            .unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    println!("{}", comb_expr.pretty(80));
    assert!(
        format!("{}", comb_expr)
            == "($ . ($ C ($ CS ($ CB I I) I) ($ C ($ B + I) 1)) ($ CBB I ($ CB I I)))"
    );
}

#[test]
pub fn conversion_compose_many() {
    let lambda_expr: RecExpr<Lambda> = COMPOSE_20_LAM.parse().unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    let comb_expr_2: RecExpr<Comb> = COMPOSE_20_COMB.parse().unwrap();
    assert!(format!("{}", comb_expr) == format!("{}", comb_expr_2));
}

#[test]
pub fn to_lam_inc() {
    let comb_expr: RecExpr<Comb> = "($ C ($ B + I) 1)".parse().unwrap();
    let lambda_expr: RecExpr<Lambda> = to_lambda_expr(&comb_expr);
    println!("{}", lambda_expr.pretty(80));
    assert!(format!("{}", lambda_expr) == "(lam x0 ($ ($ + (var x0)) 1))");
}

#[test]
pub fn to_lam_compose() {
    let comb_expr: RecExpr<Comb> = "($ CBB I ($ CB I I))".parse().unwrap();
    let lambda_expr: RecExpr<Lambda> = to_lambda_expr(&comb_expr);
    println!("{}", lambda_expr.pretty(80));
    assert!(
        format!("{}", lambda_expr)
            == "(lam x0 (lam x1 (lam x2 ($ (var x0) ($ (var x1) (var x2))))))"
    );
}

#[test]
pub fn to_lam_let() {
    let comb_expr: RecExpr<Comb> = "($ . ($ BC ($ B + I) I) 1)".parse().unwrap();
    let lambda_expr: RecExpr<Lambda> = to_lambda_expr(&comb_expr);
    println!("{}", lambda_expr.pretty(80));
    assert!(format!("{}", lambda_expr) == "($ (lam x0 (lam x1 ($ ($ + (var x1)) (var x0)))) 1)");
}

#[test]
pub fn to_lam_let_compose() {
    let comb_expr: RecExpr<Comb> =
        "($ . ($ C ($ CS ($ CB I I) I) ($ C ($ B + I) 1)) ($ CBB I ($ CB I I)))"
            .parse()
            .unwrap();
    let lambda_expr: RecExpr<Lambda> = to_lambda_expr(&comb_expr);
    println!("{}", lambda_expr.pretty(80));
    assert!(
        format!("{}", lambda_expr)
            == "($ (lam x0 ($ (lam x1 ($ ($ (var x0) (var x1)) (var x1))) (lam x2 ($ ($ + (var x2)) 1)))) (lam x3 (lam x4 (lam x5 ($ (var x3) ($ (var x4) (var x5)))))))"
    );
}

egg::test_fn! {
  apply_identity, rules(),
  "($ BB I ($ CB I I))"
  =>
  "($ CB I I)",
}

egg::test_fn! {
  assoc_under_lambda, rules(),
  "($ C ($ B + ($ C ($ B + I) 1)) 1)" // \x -> (x + 1) + 1
  =>
  "($ C ($ B + I) 2)", // x -> x + 2
}

egg::test_fn! {
  apply_1, rules(),
  "($ . ($ C ($ B + I) 1) 1)" // (\x -> x + 1) 1
  =>
  "2",
}

egg::test_fn! {
    apply_2, rules(),
    "($ . ($ S ($ B + I) I) 5)" // (\x -> x + x) 5
    =>
    "10",
}

egg::test_fn! {
    apply_3, rules(),
    "($ . ($ C ($ B + I) 1) ($ . ($ C ($ B + I) 1) 1))" // (\x -> x + 1) ((\x -> x + 1) 1)
    =>
    "3",
}

egg::test_fn! {
    compose_2, rules(),
    "($ . ($ . ($ CBB I ($ CB I I)) ($ C ($ B + I) 1))
        ($ C ($ B + I) 1))" // compose inc inc
    =>
    "($ C ($ B + I) 2)", // x -> x + 2
}

#[test]
pub fn compose_8() {
    let source: RecExpr<Comb> = COMPOSE_8_COMB.parse().unwrap();
    egg::test::test_runner(
        "compose_8",
        None,
        &(rules()),
        source,
        &["($ C ($ B + I) 8)".parse().unwrap()],
        None,
        true,
    )
}

#[test]
pub fn compose_20() {
    let source: RecExpr<Comb> = COMPOSE_20_COMB.parse().unwrap();
    egg::test::test_runner(
        "compose_20",
        None,
        &(rules()),
        source,
        &["($ C ($ B + I) 20)".parse().unwrap()],
        None,
        true,
    )
}

#[test]
pub fn compose_2_from_lambda() {
    let lambda_expr: RecExpr<Lambda> =
        "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
                                            (let add1 (lam x ($ ($ + (var x)) 1))
                                            ($ ($ (var compose) (var add1)) (var add1))))"
            .parse()
            .unwrap();
    let source = from_lambda_expr(&lambda_expr);
    egg::test::test_runner(
        "compose_2_from_lambda",
        None,
        &(rules()),
        source,
        &["($ C ($ B + I) 2)".parse().unwrap()],
        None,
        true,
    )
}

#[test]
pub fn compose_20_from_lambda() {
    let lambda_expr: RecExpr<Lambda> = COMPOSE_20_LAM.parse().unwrap();
    let source = from_lambda_expr(&lambda_expr);
    egg::test::test_runner(
        "compose_20_from_lambda",
        None,
        &(rules()),
        source,
        &["($ C ($ B + I) 20)".parse().unwrap()],
        None,
        true,
    )
}

#[test]
pub fn compose_20_id() {
    let lambda_expr: RecExpr<Lambda> = COMPOSE_20_ID.parse().unwrap();
    let source = from_lambda_expr(&lambda_expr);
    egg::test::test_runner(
        "compose_20_id",
        None,
        &(rules()),
        source,
        &["I".parse().unwrap()],
        None,
        true,
    )
}

#[test]
pub fn comb_print() {
    // let source_expr_lambda: RecExpr<Lambda> = "($ (lam x ($ ($ + (var x)) (var x))) 5)".parse().unwrap();
    // let source_expr_lambda: RecExpr<Lambda> = "($ (lam x ($ ($ + (var x)) 1)) ($ (lam x ($ ($ + (var x)) 1)) 5))".parse().unwrap();
    // let source_expr_lambda: RecExpr<Lambda> = "($ (lam f (lam g (lam x ($ (var f) ($ (var g) (var x)))))) (lam x ($ ($ + (var x)) 1)))".parse().unwrap();
    // let source_expr_lambda: RecExpr<Lambda> = "($ ($ (lam f (lam g (lam x ($ (var f) ($ (var g) (var x)))))) (lam x (var x))) (lam x (var x)))".parse().unwrap();
    // let source_expr_lambda: RecExpr<Lambda> = "($ ($ (lam f (lam g (lam x ($ (var f) ($ (var g) (var x)))))) (lam x ($ ($ + (var x)) 1))) (lam x ($ ($ + (var x)) 1)))".parse().unwrap();
    // let source_expr_lambda: RecExpr<Lambda> = "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
    //                                             (let add1 (lam x ($ ($ + (var x)) 1))
    //                                             ($ ($ (var compose) (var add1)) (var add1))))".parse().unwrap();
    let source_expr_lambda: RecExpr<Lambda> = COMPOSE_20_ID.parse().unwrap();
    let source_expr = from_lambda_expr(&source_expr_lambda);
    println!("Source: {}", source_expr);

    // Create a runner with named::rules and from source_expr:
    let runner = Runner::default()
        .with_expr(&source_expr)
        .with_iter_limit(100)
        // .with_time_limit(std::time::Duration::from_secs(10))
        // .with_node_limit(100)
        .run(&rules());

    println!("Stop reason: {:?}", runner.stop_reason.unwrap());

    println!("E-classes: {}", runner.egraph.classes().count());
    println!("E-nodes: {}", runner.egraph.total_size());

    // Print the best expression from each eclass in the runner's egraph:
    let extractor = Extractor::new(&runner.egraph, AstSize);
    for eclass in runner.egraph.classes() {
        let expr = extractor.find_best(eclass.id).1;
        println!("{}: {}", eclass.id, expr);
    }
}
