use egg::{rewrite as rw, *};

use crate::named::{var_symbol, Lambda, COMPOSE_20_LAM};
use fxhash::FxHashMap as HashMap;
use fxhash::FxHashSet as HashSet;

define_language! {
    /// A language if CBSI combinators from
    /// Liang, Jordan, Klein. "Learning Programs: A Hierarchical Bayesian Approach. ICML 2010"
    pub enum Comb {
        Num(i32),
        "I" = I, // identity
        "C" = C, // route left
        "B" = B, // route right
        "S" = S,  // route both
        "." = Nil, // empty list of routers
        ":" = Cons([Id; 2]), // non-empty list of routers
        "$" = App([Id; 3]), // first child is a list of routers, second is the function, third is the argument
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
}

/// Convert a list of routers into a combinator expression added to the given expression
fn add_routers(expr: &mut RecExpr<Comb>, routers: &[Comb]) -> Id {
    let mut current = expr.add(Comb::Nil);

    for router in routers.iter().rev() {
        let lhs = expr.add(router.clone());
        let new_current = expr.add(Comb::Cons([lhs, current]));
        current = new_current;
    }
    current
}

/// Convert a combinator expression that represents a list of routers into a vector of routers
/// (this is the inverse of add_routers)
fn get_routers(expr: &RecExpr<Comb>, routers_id: Id) -> Vec<Comb> {
    let mut routers = vec![];
    let mut current = routers_id;
    while let Comb::Cons([lhs, rhs]) = &expr[current] {
        routers.push(expr[*lhs].clone());
        current = *rhs;
    }
    routers
}

/// Partition a list of variables into a left and right lists accoridng to the routers
fn route_vars(vars: &[egg::Symbol], routers: &[Comb]) -> (Vec<egg::Symbol>, Vec<egg::Symbol>) {
    assert!(routers.len() >= vars.len()); // all variables must be routed
    let mut left_vars = vec![];
    let mut right_vars = vec![];
    for (router, var) in routers.iter().zip(vars.iter()) {
        match router {
            Comb::C => {
                left_vars.push(*var);
            }
            Comb::B => {
                right_vars.push(*var);
            }
            Comb::S => {
                left_vars.push(*var);
                right_vars.push(*var);
            }
            _ => panic!("not a router"),
        }
    }
    (left_vars, right_vars)
}

/// Convert a lambda expression into a combinator expression
pub fn from_lambda_expr(expr: &RecExpr<Lambda>) -> RecExpr<Comb> {
    // First pass: compute the set of free variables for every node and remember where each variable is bound
    let mut free_vars = vec![HashSet::default(); expr.as_ref().len()];
    let mut var_bindings = HashMap::default();

    for (id, node) in expr.as_ref().iter().enumerate() {
        match node {
            Lambda::Var(var_id) => {
                free_vars[id].insert(var_symbol(expr, *var_id));
            }
            Lambda::App([l, r]) => {
                let mut res = free_vars[usize::from(*l)].clone();
                res.extend(free_vars[usize::from(*r)].iter());
                free_vars[id] = res;
            }
            Lambda::Lambda([var_id, body]) => {
                let mut res = free_vars[usize::from(*body)].clone();
                let var_symbol = var_symbol(expr, *var_id);
                res.remove(&var_symbol);
                free_vars[id] = res;
                var_bindings.insert(var_symbol, id);
            }
            Lambda::Let([var_id, value, body]) => {
                let mut res = free_vars[usize::from(*value)].clone();
                res.extend(free_vars[usize::from(*body)].iter());
                let var_symbol = var_symbol(expr, *var_id);
                res.remove(&var_symbol);
                free_vars[id] = res;
                var_bindings.insert(var_symbol, id);
            }
            _ => (),
        }
    }

    // Second pass: gradually add nodes to the combinator expression
    // - replacing variables with I
    // - skipping lambdas
    // - inserting appropriate routers at each application based on the free variables of the children
    // - translating lets into applications
    let mut res = RecExpr::default();
    let mut mapping = HashMap::default(); // maps from lambda node id to combinator node id
    for (id, node) in expr.as_ref().iter().enumerate() {
        let new_id = match node {
            Lambda::Num(n) => res.add(Comb::Num(*n)),
            Lambda::Symbol(s) => res.add(Comb::Symbol(*s)),
            Lambda::Var(_) => res.add(Comb::I),
            Lambda::Lambda([_, body]) => mapping[&usize::from(*body)], // skip lambdas, but map them to the translation of their body, in case they are referenced by some application or let
            Lambda::App([l, r]) => add_application(
                &mut res,
                id,
                usize::from(*l),
                usize::from(*r),
                &free_vars,
                &var_bindings,
                &mapping,
            ),
            Lambda::Let([_, value, body]) => add_application(
                &mut res,
                id,
                usize::from(*body),
                usize::from(*value),
                &free_vars,
                &var_bindings,
                &mapping,
            ),
            Lambda::Add(_) => unreachable!("Add cannot occur in surface language"),
        };
        mapping.insert(id, new_id);
    }

    res
}

/// Helper function for converting a named lambda calculus expression into a combinator expression;
/// this function adds an application with appropriate routers
fn add_application(
    expr: &mut RecExpr<Comb>, // combinator expression under construction
    parent: usize,            // index of current application node in named expression
    left: usize,              // index of left child in named expression
    right: usize,             // index of right child in named expression
    free_vars: &Vec<HashSet<egg::Symbol>>, // index of free variables in named expression
    var_bindings: &HashMap<egg::Symbol, usize>, // index of variable bindings in named expression
    mapping: &HashMap<usize, Id>, // mapping from named expression indices to combinator expression indices
) -> Id {
    // order my own free variables by the order in which they are bound:
    let mut ordered_vars = free_vars[parent].iter().collect::<Vec<_>>();
    ordered_vars.sort_unstable_by_key(|var_id| std::cmp::Reverse(var_bindings[var_id]));

    // compute the router for each variable based on which children contain it free:
    let mut routers = vec![];
    for var_id in ordered_vars {
        let left_contains = free_vars[left].contains(var_id);
        let right_contains = free_vars[right].contains(var_id);
        if left_contains && right_contains {
            routers.push(Comb::S);
        } else if left_contains {
            routers.push(Comb::C);
        } else if right_contains {
            routers.push(Comb::B);
        }
    }

    // add the routers and then the application
    let r_id = add_routers(expr, &routers);
    expr.add(Comb::App([r_id, mapping[&left], mapping[&right]]))
}

/// Convert a combinator expression into a lambda expression
pub fn to_lambda_expr(expr: &RecExpr<Comb>) -> RecExpr<Lambda> {
    // First pass: compute a mapping from I-nodes to variables and from "abstraction" nodes to variables they bind
    let mut var_mapping = HashMap::default();
    let mut total_vars = 0;
    compute_vars(
        expr,
        &mut var_mapping,
        &mut total_vars,
        &vec![],
        Id::from(expr.as_ref().len() - 1),
    );

    println!("expr: {:?}", expr);
    println!("var_mapping: {:?}", var_mapping);

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
                println!("accessing var_mapping[{:?}]", Id::from(id));
                let vars = &var_mapping[&Id::from(id)];
                assert!(vars.len() == 1);
                let s_id = res.add(Lambda::Symbol(vars[0]));
                res.add(Lambda::Var(s_id))
            }
            Comb::App([_, l, r]) => {
                println!("accessing var_mapping[{:?}]", Id::from(id));
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
            Comb::B | Comb::C | Comb::S | Comb::Nil | Comb::Cons(_) => Id::from(0), // skip those nodes, we already took care of them in the first pass
            Comb::Add(_) => unreachable!("Add cannot occur in surface language"),
        };
        mapping.insert(Id::from(id), new_id);
    }
    res
}

fn compute_vars(
    expr: &RecExpr<Comb>,
    var_mapping: &mut HashMap<Id, Vec<egg::Symbol>>,
    total_vars: &mut usize,
    vars: &Vec<egg::Symbol>,
    id: Id,
) {
    let node = &expr[id];
    match node {
        Comb::I => {
            assert!(vars.len() == 1);
            let var = vars[0];
            var_mapping.insert(id, vec![var]);
        }
        Comb::App([route, l, r]) => {
            let routers = get_routers(expr, *route);
            assert!(routers.len() >= vars.len()); // at least we have routers for all variables that are already bound!
            if routers.len() == vars.len() {
                // no new variables are bound
                var_mapping.insert(id, vec![]);
                let (l_vars, r_vars) = route_vars(vars, &routers);
                compute_vars(expr, var_mapping, total_vars, &l_vars, *l);
                compute_vars(expr, var_mapping, total_vars, &r_vars, *r);
            } else {
                // new variables are bound
                let mut new_vars = vec![];
                for _ in routers[vars.len()..].iter() {
                    let var = egg::Symbol::from(format!("x{}", total_vars));
                    *total_vars += 1;
                    new_vars.push(var);
                }
                let all_vars = [&vars[..], &new_vars[..]].concat();
                var_mapping.insert(id, new_vars);
                let (l_vars, r_vars) = route_vars(&all_vars, &routers);
                compute_vars(expr, var_mapping, total_vars, &l_vars, *l);
                compute_vars(expr, var_mapping, total_vars, &r_vars, *r);
            }
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
        if to.constant.is_none() && from.constant.is_some() {
            to.constant = from.constant;
            DidMerge(true, false)
        } else {
            DidMerge(false, true)
        }
    }

    fn make(egraph: &EGraph, enode: &Comb) -> Data {
        let constant = eval(egraph, enode);
        Data { constant }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant.clone() {
            let const_id = egraph.add(c);
            egraph.union(id, const_id);
        }
    }
}

fn rules() -> Vec<Rewrite<Comb, CombAnalysis>> {
    vec![
        rw!("add-assoc-0"; "($ . ($ . + ($ . ($ . + ?a) ?b)) ?c)" => "($ . ($ . + ?a) ($ . ($ . + ?b) ?c))"),
        rw!("add-assoc-1"; "($ (: C .) ($ (: B .) + ($ (: C .) ($ (: B .) + ?a) ?b)) ?c)" => 
                           "($ (: C .) ($ (: B .) + ?a) ($ . ($ . + ?b) ?c))"),
        rw!("id"; "($ . I ?x)" => "?x"),
        rw!("id-b"; "($ (: B .) I ?x)" => "?x"),
        rw!("beta-b"; "($ . ($ (: B ?r) ?x ?y) ?z)"          => "($ ?r ?x ($ . ?y ?z))"),
        rw!("beta-c"; "($ . ($ (: C ?r) ?x ?y) ?z)"          => "($ ?r ($ . ?x ?z) ?y)"),
        rw!("beta-s"; "($ . ($ (: S ?r) ?x ?y) ?z)"          => "($ ?r ($ . ?x ?z) ($ . ?y ?z))"),
        rw!("beta-b-under-b"; "($ (: B .) ($ (: B ?r) ?x ?y) ?z)"   => "($ (: B ?r) ?x ($ (: B .) ?y ?z))"),
        rw!("beta-c-under-b"; "($ (: B .) ($ (: C ?r) ?x ?y) ?z)"   => "($ (: C ?r) ($ (: B .) ?x ?z) ?y)"),
    ]
}

///////// Tests ///////////

static COMPOSE_20_COMB: &str = "($ . ($ (: C .) 
        ($ (: S (: S .)) ($ (: C (: B .)) I I) 
            ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                    ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                        ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                            ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                    ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                        ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                            ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                    ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                        ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                            ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                                ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                                    ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                                        ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                                            ($ (: S (: S .)) ($ (: C (: B .)) I I) 
                                                                            ($ (: C (: S .)) ($ (: C (: B .)) I I) I)))))))))))))))))))
            ($ (: C .) ($ (: B .) + I) 1))
            ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)))";

#[test]
pub fn conversion_inc() {
    let lambda_expr: RecExpr<Lambda> = "(lam y ($ ($ + (var y)) 1))".parse().unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    assert!(format!("{}", comb_expr) == "($ (: C .) ($ (: B .) + I) 1)");
    println!("{}", comb_expr.pretty(80));
}

#[test]
pub fn conversion_compose() {
    let lambda_expr: RecExpr<Lambda> = "(lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))"
        .parse()
        .unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    assert!(format!("{}", comb_expr) == "($ (: C (: B (: B .))) I ($ (: C (: B .)) I I))");
    println!("{}", comb_expr.pretty(80));
}

#[test]
pub fn conversion_let() {
    let lambda_expr: RecExpr<Lambda> = "(let x 1 (lam y ($ ($ + (var y)) (var x))))"
        .parse()
        .unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    assert!(format!("{}", comb_expr) == "($ . ($ (: B (: C .)) ($ (: B .) + I) I) 1)");
    println!("{}", comb_expr.pretty(80));
}

#[test]
pub fn conversion_let_compose() {
    let lambda_expr: RecExpr<Lambda> =
        "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
                                        (let add1 (lam y ($ ($ + (var y)) 1))
                                        ($ ($ (var compose) (var add1)) (var add1))))"
            .parse()
            .unwrap();
    let comb_expr = from_lambda_expr(&lambda_expr);
    assert!(format!("{}", comb_expr) == "($ . ($ (: C .) ($ (: C (: S .)) ($ (: C (: B .)) I I) I) ($ (: C .) ($ (: B .) + I) 1)) ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)))");
    println!("{}", comb_expr.pretty(80));
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
    let comb_expr: RecExpr<Comb> = "($ (: C .) ($ (: B .) + I) 1)".parse().unwrap();
    let lambda_expr: RecExpr<Lambda> = to_lambda_expr(&comb_expr);
    assert!(format!("{}", lambda_expr) == "(lam x0 ($ ($ + (var x0)) 1))");
    println!("{}", lambda_expr.pretty(80));
}

#[test]
pub fn to_lam_compose() {
    let comb_expr: RecExpr<Comb> = "($ (: C (: B (: B .))) I ($ (: C (: B .)) I I))"
        .parse()
        .unwrap();
    let lambda_expr: RecExpr<Lambda> = to_lambda_expr(&comb_expr);
    assert!(
        format!("{}", lambda_expr)
            == "(lam x0 (lam x1 (lam x2 ($ (var x0) ($ (var x1) (var x2))))))"
    );
    println!("{}", lambda_expr.pretty(80));
}

// #[test]
// pub fn conversion_let() {
//     let lambda_expr: RecExpr<Lambda> = "(let x 1 (lam y ($ ($ + (var y)) (var x))))"
//         .parse()
//         .unwrap();
//     let comb_expr = from_lambda_expr(&lambda_expr);
//     assert!(format!("{}", comb_expr) == "($ . ($ (: B (: C .)) ($ (: B .) + I) I) 1)");
//     println!("{}", comb_expr.pretty(80));
// }

// #[test]
// pub fn conversion_let_compose() {
//     let lambda_expr: RecExpr<Lambda> =
//         "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
//                                         (let add1 (lam y ($ ($ + (var y)) 1))
//                                         ($ ($ (var compose) (var add1)) (var add1))))"
//             .parse()
//             .unwrap();
//     let comb_expr = from_lambda_expr(&lambda_expr);
//     assert!(format!("{}", comb_expr) == "($ . ($ (: C .) ($ (: C (: S .)) ($ (: C (: B .)) I I) I) ($ (: C .) ($ (: B .) + I) 1)) ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)))");
//     println!("{}", comb_expr.pretty(80));
// }

egg::test_fn! {
  assoc_under_lambda, rules(),
  "($ (: C .) ($ (: B .) + ($ (: C .) ($ (: B .) + I) 1)) 1)" // \x -> (x + 1) + 1
  =>
  "($ (: C .) ($ (: B .) + I) 2)", // x -> x + 2
}

egg::test_fn! {
  apply, rules(),
  "($ . ($ (: C .) ($ (: B .) + I) 1) 1)" // (\x -> x + 1) 1
  =>
  "2",
}

egg::test_fn! {
    compose_2, rules(),
    "($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
        ($ (: C .) ($ (: B .) + I) 1))" // compose inc inc
    =>
    "($ (: C .) ($ (: B .) + I) 2)", // x -> x + 2
}

#[test]
pub fn compose_20() {
    let source: RecExpr<Comb> = COMPOSE_20_COMB.parse().unwrap();
    egg::test::test_runner(
        "compose_20",
        None,
        &(rules()),
        source,
        &["($ (: C .) ($ (: B .) + I) 20)".parse().unwrap()],
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
        &["($ (: C .) ($ (: B .) + I) 20)".parse().unwrap()],
        None,
        true,
    )
}
