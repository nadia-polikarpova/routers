use egg::{rewrite as rw, *};

use crate::named::{Lambda, var_symbol};
use fxhash::FxHashMap as HashMap;
use fxhash::FxHashSet as HashSet;

define_language! {
    /// A language if CBSI combinators from
    /// Liang, Jordan, Klein. "Learning Programs: A Hierarchical Bayesian Approach. ICML 2010"
    enum Comb {
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

fn add_application(
    expr: &mut RecExpr<Comb>,
    parent: usize,
    left: usize,
    right: usize,
    free_vars: &Vec<HashSet<egg::Symbol>>,
    var_bindings: &HashMap<egg::Symbol, usize>,
    mapping: &HashMap<usize, Id>,
) -> Id {
    // order my own free variables by the order in which they are bound
    let mut ordered_vars = free_vars[parent].iter().collect::<Vec<_>>();
    ordered_vars.sort_by_key(|var_id| std::cmp::Reverse(var_bindings[var_id]));
    // println!("ordered_vars: {:?}", ordered_vars);

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
    let r_id = add_routers(expr, &routers);
    expr.add(Comb::App([r_id, mapping[&left], mapping[&right]]))
}

// Convert a lambda expression into a combinator expression
fn from_rec_lambda_expr(expr: &RecExpr<Lambda>) -> RecExpr<Comb> {
    // First pass: compute the set of free variables for every node and remember where each variable is bound
    let mut free_vars = vec![HashSet::default(); expr.as_ref().len()];
    let mut var_bindings = HashMap::default();

    for (id, node) in expr.as_ref().iter().enumerate() {
        match node {
            Lambda::Var(var_id) => {
                // free_vars[id].insert(*var_id);
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
    // println!("expr: {:?}", expr);
    // println!("free_vars: {:?}", free_vars);
    // println!("var_bindings: {:?}", var_bindings);

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

#[derive(Default)]
struct CombAnalysis;

#[derive(Debug)]
struct Data {
    constant: Option<Comb>,
}

type EGraph = egg::EGraph<Comb, CombAnalysis>;

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

static COMPOSE_20_LAM: &str = "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
     (let add1 (lam y ($ ($ + (var y)) 1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
        ($ ($ (var compose) (var add1))
                            (var add1))))))))))))))))))))))";

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
            ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)))"; // analogue of lambda example with the lets

#[test]
pub fn conversion_inc() {
    let lambda_expr: RecExpr<Lambda> = "(lam y ($ ($ + (var y)) 1))".parse().unwrap();
    let comb_expr = from_rec_lambda_expr(&lambda_expr);
    assert!(format!("{}", comb_expr) == "($ (: C .) ($ (: B .) + I) 1)");
    println!("{}", comb_expr.pretty(80));
}

#[test]
pub fn conversion_compose() {
    let lambda_expr: RecExpr<Lambda> = "(lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))"
        .parse()
        .unwrap();
    let comb_expr = from_rec_lambda_expr(&lambda_expr);
    assert!(format!("{}", comb_expr) == "($ (: C (: B (: B .))) I ($ (: C (: B .)) I I))");
    println!("{}", comb_expr.pretty(80));
}

#[test]
pub fn conversion_let() {
    let lambda_expr: RecExpr<Lambda> = "(let x 1 (lam y ($ ($ + (var y)) (var x))))"
        .parse()
        .unwrap();
    let comb_expr = from_rec_lambda_expr(&lambda_expr);
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
    let comb_expr = from_rec_lambda_expr(&lambda_expr);
    assert!(format!("{}", comb_expr) == "($ . ($ (: C .) ($ (: C (: S .)) ($ (: C (: B .)) I I) I) ($ (: C .) ($ (: B .) + I) 1)) ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)))");
    println!("{}", comb_expr.pretty(80));
}

#[test]
pub fn conversion_compose_many() {
    let lambda_expr: RecExpr<Lambda> = COMPOSE_20_LAM.parse().unwrap();
    let comb_expr = from_rec_lambda_expr(&lambda_expr);
    let comb_expr_2: RecExpr<Comb> = COMPOSE_20_COMB.parse().unwrap();
    assert!(format!("{}", comb_expr) == format!("{}", comb_expr_2));
}

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
    let source = from_rec_lambda_expr(&lambda_expr);
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
