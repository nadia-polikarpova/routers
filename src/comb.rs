use egg::{rewrite as rw, *};

// enum Router {
//     C, // route left
//     B, // route right
//     S  // route both
// }

define_language! {
    enum Comb {
        Num(i32),
        "+" = Plus,

        "I" = I, // identity
        "C" = C, // route left
        "B" = B, // route right
        "S" = S,  // route both
        "." = Nil, // empty list of routers
        ":" = Cons([Id; 2]), // non-empty list of routers

        "$" = App([Id; 3]), // first child is a list of routers, second is the function, third is the argument

        Add(i32), // partially applied plus, used during constant folding

        Symbol(egg::Symbol),
    }
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
        Comb::Num(_) | Comb::Plus => Some(enode.clone()),
        Comb::App([route, l,r]) => {
            match (x(l)?, x(r)?) {
                (Comb::Plus, Comb::Num(n)) => Some(Comb::Add(*n)),
                (Comb::Add(n), Comb::Num(m)) => Some(Comb::Num(n + m)),
                _ => None,
            }
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

egg::test_fn! {
    compose_no_let_20, rules(),
    "($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
        ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
            ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                    ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                        ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                            ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                    ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                        ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                            ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                    ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                        ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                            ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                                ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                                    ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                                        ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                                            ($ . ($ . ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I)) ($ (: C .) ($ (: B .) + I) 1))
                                                                                ($ (: C .) ($ (: B .) + I) 1))))))))))))))))))))" // compose inc ... (compose inc inc)
    =>
    "($ (: C .) ($ (: B .) + I) 20)", // x -> x + 20
}

egg::test_fn! {
    compose_20, rules(),
    "($ . ($ . 
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
        ($ (: C (: B (: B .))) I ($ (: C (: B .)) I I))) 
        ($ (: C .) ($ (: B .) + I) 1))" // analogue of lambda example with the lets
    =>
    "($ (: C .) ($ (: B .) + I) 20)", // x -> x + 20
}