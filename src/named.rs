use egg::{rewrite as rw, *};
use fxhash::FxHashSet as HashSet;

define_language! {
    /// Regular named lambda calculus with integers and addition
    /// (mostly stolen from egg's tests, but addition is not built-in)
    pub enum Lambda {
        Num(i32),
        "var" = Var(Id),
        // "+" = Plus,
        "$" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),
        "let" = Let([Id; 3]),
        Symbol(egg::Symbol), // everything else, including +
        Add(i32), // partially applied plus, used only during constant folding
    }
}

impl Lambda {
    pub fn symbol(&self) -> egg::Symbol {
        match self {
            Lambda::Symbol(s) => *s,
            _ => panic!("not a symbol"),
        }
    }

    pub fn is_plus(&self) -> bool {
        match self {
            Lambda::Symbol(s) => s == &egg::Symbol::from("+"),
            _ => false,
        }
    }
}

pub fn var_symbol(expr: &RecExpr<Lambda>, var_id: Id) -> egg::Symbol {
    expr[var_id].symbol()
}

type EGraph = egg::EGraph<Lambda, LambdaAnalysis>;

#[derive(Default)]
struct LambdaAnalysis;

#[derive(Debug)]
struct Data {
    free: HashSet<Id>,
    constant: Option<Lambda>,
}

fn eval(egraph: &EGraph, enode: &Lambda) -> Option<Lambda> {
    let x = |i: &Id| egraph[*i].data.constant.as_ref();
    match enode {
        Lambda::Num(_) => Some(enode.clone()),
        _ if enode.is_plus() => Some(enode.clone()),
        Lambda::App([l, r]) => match (x(l)?, x(r)?) {
            (l_const, Lambda::Num(n)) if l_const.is_plus() => Some(Lambda::Add(*n)),
            (Lambda::Add(n), Lambda::Num(m)) => Some(Lambda::Num(n + m)),
            _ => None,
        },
        _ => None,
    }
}

impl Analysis<Lambda> for LambdaAnalysis {
    type Data = Data;
    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        let before_len = to.free.len();
        // to.free.extend(from.free);
        to.free.retain(|i| from.free.contains(i));
        if to.constant.is_none() && from.constant.is_some() {
            to.constant = from.constant;
            DidMerge(true, to.free.len() != from.free.len())
        } else {
            DidMerge(before_len != to.free.len(), true)
        }
    }

    fn make(egraph: &EGraph, enode: &Lambda) -> Data {
        let f = |i: &Id| egraph[*i].data.free.iter().cloned();
        let mut free = HashSet::default();
        match enode {
            Lambda::Var(v) => {
                free.insert(*v);
            }
            Lambda::Let([v, a, b]) => {
                free.extend(f(b));
                free.remove(v);
                free.extend(f(a));
            }
            Lambda::Lambda([v, a]) => {
                free.extend(f(a));
                free.remove(v);
            }
            _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        }
        let constant = eval(egraph, enode);
        Data { constant, free }
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

fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn is_const(v: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v]].data.constant.is_some()
}

fn rules() -> Vec<Rewrite<Lambda, LambdaAnalysis>> {
    vec![
        rw!("add-assoc"; "($ ($ + ($ ($ + ?a) ?b)) ?c)" => "($ ($ + ?a) ($ ($ + ?b) ?c))"),
        rw!("beta";     "($ (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rw!("let-app";  "(let ?v ?e ($ ?a ?b))" => "($ (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-const";
            "(let ?v ?e ?c)" => "?c" if is_const(var("?c"))),
        rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
        rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-lam-same"; "(let ?v1 ?e (lam ?v1 ?body))" => "(lam ?v1 ?body)"),
        rw!("let-lam-diff";
            "(let ?v1 ?e (lam ?v2 ?body))" =>
            { CaptureAvoid {
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(lam ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(lam ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
    ]
}

struct CaptureAvoid {
    fresh: Var,
    v2: Var,
    e: Var,
    if_not_free: Pattern<Lambda>,
    if_free: Pattern<Lambda>,
}

impl Applier<Lambda, LambdaAnalysis> for CaptureAvoid {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<Lambda>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let e = subst[self.e];
        let v2 = subst[self.v2];
        let v2_free_in_e = egraph[e].data.free.contains(&v2);
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = Lambda::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_free
                .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
        } else {
            self.if_not_free
                .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
        }
    }
}

///////// Tests ///////////

/// Function composition and increment nested 20 times.
pub static COMPOSE_20_LAM: &str =
    "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
     (let add1 (lam x ($ ($ + (var x)) 1))
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

egg::test_fn! {
  lambda_under, rules(),
  "(lam x ($ ($ + 4)
             ($ (lam y (var y)) 4)))"
  =>
  "(lam x 8))",
}

#[test]
pub fn lambda_compose_many() {
    let source: RecExpr<Lambda> = COMPOSE_20_LAM.parse().unwrap();
    egg::test::test_runner(
        "compose_20",
        None,
        &(rules()),
        source,
        &["(lam ?x ($ ($ + (var ?x)) 20))".parse().unwrap()],
        None,
        true,
    )
}

#[test]
pub fn lambda_print() {
    // let source_expr: RecExpr<Lambda> = "($ (lam x ($ ($ + (var x)) (var x))) 5)".parse().unwrap();
    // let source_expr: RecExpr<Lambda> = "($ (lam x ($ ($ + (var x)) 1)) ($ (lam x ($ ($ + (var x)) 1)) 5))".parse().unwrap();
    // let source_expr: RecExpr<Lambda> = "($ (lam f (lam g (lam x ($ (var f) ($ (var g) (var x)))))) (lam x ($ ($ + (var x)) 1)))".parse().unwrap();
    // let source_expr: RecExpr<Lambda> = "($ ($ (lam f (lam g (lam x ($ (var f) ($ (var g) (var x)))))) (lam x ($ ($ + (var x)) 1))) (lam x ($ ($ + (var x)) 1)))".parse().unwrap();
    // let source_expr: RecExpr<Lambda> = "(let compose (lam f (lam g (lam x ($ (var f) ($ (var g) (var x))))))
    //                                         (let add1 (lam x ($ ($ + (var x)) 1))
    //                                         ($ ($ (var compose) (var add1)) (var add1))))".parse().unwrap();
    let source_expr: RecExpr<Lambda> = COMPOSE_20_LAM.parse().unwrap();

    // Create a runner with named::rules and from source_expr:
    let runner = Runner::default()
        .with_expr(&source_expr)
        .with_iter_limit(100)
        // .with_time_limit(std::time::Duration::from_secs(10))
        // .with_node_limit(100000)
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
