#![allow(unused)]
#![allow(non_snake_case)]

use crate::*;

define_language! {
    pub enum Arith2 {
        Var(Slot) = "var",
        F(AppliedId, AppliedId) = "f",
        Sub(AppliedId, AppliedId) = "sub",
        Lam(Bind<AppliedId>) = "lam",
        Zero() = "zero",
    }
}

fn subxx() -> Rewrite<Arith2> { Rewrite::new("subxx", "(sub ?x ?x)", "zero") }
fn subxx2() -> Rewrite<Arith2> { Rewrite::new("subxx2", "zero", "(sub (var $x) (var $x))") }
fn special() -> Rewrite<Arith2> { Rewrite::new("special", "(f (sub ?x ?x) (sub ?x ?x))", "zero") }
fn special2() -> Rewrite<Arith2> { Rewrite::new("special2", "(f ?x (sub ?x ?x))", "zero") }

#[test]
fn redundancy_matching_bug2() {
    let x = "(f zero zero)";
    let y = "zero";

    let rewrites = &[
        special(),
        subxx(),
        subxx2(),
    ];
    assert_reaches(x, y, rewrites, 3);
}

#[test]
// In this version of the bug, a fresh/redundant variable has to alias a non-redundant variable. So that is also possible.
fn redundancy_matching_bug3() {
    let x = "(f (var $x) zero)";
    let y = "zero";

    let rewrites = &[
        subxx(),
        special2(),
    ];
    assert_reaches(x, y, rewrites, 3);
}



#[test]
fn multipat_test() {
    let mut eg: EGraph<Arith2> = EGraph::new(());
    eg.add_expr(RecExpr::parse("(f (var $x) zero)").unwrap());
    let pat: MultiPattern<Arith2> = MultiPattern::parse("?x == (f ?a ?b), ?b == zero").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 1);
}

#[test]
fn multipat_test2() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(f (var $x) (sub (var $y) (var $y)))").unwrap());

    let a = eg.add_expr(RecExpr::parse("(sub (var $z) (var $z))").unwrap());
    let b = eg.add_expr(RecExpr::parse("zero").unwrap());
    eg.union(&a, &b);

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (f ?a ?b), ?b == (sub ?a ?a)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 1);
}

#[test]
fn multipat_test3() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(var $x)").unwrap());

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (var $y)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 1);
    let m = &matches[0];
    assert_eq!(m["out"].m.values(), std::iter::once(Slot::named("y")).collect());
}

#[test]
fn multipat_test4() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(f (var $x) (sub (var $y) (var $y)))").unwrap());

    let a = eg.add_expr(RecExpr::parse("(sub (var $z) (var $z))").unwrap());
    let b = eg.add_expr(RecExpr::parse("zero").unwrap());
    eg.union(&a, &b);

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (f ?a ?b), ?b == (sub ?c ?a), ?c == (var $x)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 1);
}

#[test]
fn multipat_test5() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(sub (var $x) (var $y))").unwrap());

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (sub ?a ?a), ?a == (var $a)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert!(matches.is_empty());
}

#[test]
fn multipat_test6() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(sub (var $x) (var $y))").unwrap());

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (sub ?a ?a)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert!(matches.is_empty());
}

#[test]
fn multipat_test7() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(sub (var $x) (var $x))").unwrap());

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (sub ?a ?a), ?a == (var $a)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 1);
}

#[test]
fn multipat_test8() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(sub (var $x) (var $x))").unwrap());

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (sub ?a ?a)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 1);
}

#[test]
fn multipat_test9() {
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(f (var $x) (sub (var $y) (var $y)))").unwrap());

    let a = eg.add_expr(RecExpr::parse("(sub (var $z) (var $z))").unwrap());
    let b = eg.add_expr(RecExpr::parse("zero").unwrap());
    eg.union(&a, &b);

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (f ?a ?b), ?b == (sub ?c ?c)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 2);
    // There are two matches because ?a and ?c can agree or disagree on their slot. f($x, $y-$y) versus f($x, $x-$x).
}

#[test]
fn multipat_test10() { // testcase found by oflatt-claude.
    let mut eg: EGraph<Arith2> = EGraph::new(());

    eg.add_expr(RecExpr::parse("(lam $x (var $x))").unwrap());

    let pat: MultiPattern<Arith2> = MultiPattern::parse("?out == (lam $v ?b)").unwrap();
    let matches = multi_ematch(&pat, &eg);
    dbg!(&matches);
    assert_eq!(matches.len(), 1);

    let m = &matches[0];
    let vals = &m["b"].m.values();
    let correct_vals = std::iter::once(Slot::named("v")).collect();

    assert_eq!(*vals, correct_vals);
}

#[test]
// A class with a slot symmetry has more readings than nodes: `(f a (f b z))` unioned
// with `(f b (f a z))` gives the class the swap `a <-> b`, and the one stored node stands
// for both. The nested matcher enumerates them, `ematch_impl` matching every
// group-compatible variant of a node. The multipattern matcher does not: for a pattern
// variable's class it matches the stored node only, so under a binder whose bound slot
// is the stored first argument,
//
//     (lam $0 (f (var $0) (f (var $1) (var $2))))          the term
//     (lam $x (f ?e1 ?e2))  =>  (f ?e1 (lam $x ?e2))       the rewrite, when `$x` is not free in `?e1`
//
// it offers `?e1 = (var $0)` only, the guard refuses it, and the sound firing with
// `?e1 = (var $1)` never happens. The paper's SDQL rules reach this in the TTM
// kernel: `sing-mult-1`/`sing-mult-2` derive `(sing a (sing b x)) = (sing b (sing a x))`,
// after which `sum-fact-3` cannot pull the free key out of a sum whose stored node has
// the bound key first, and the target of the first phase is not reached.
fn multipat_matches_every_symmetric_reading() {
    let term = "(lam $0 (f (var $0) (f (var $1) (var $2))))";
    let sym_a = "(f (var $1) (f (var $3) (var $2)))";
    let sym_b = "(f (var $3) (f (var $1) (var $2)))";
    let lhs = "(lam $x (f ?e1 ?e2))";
    let rhs = "(f ?e1 (lam $x ?e2))";
    let goal = "(f (var $1) (lam $0 (f (var $0) (var $2))))";
    let x = Slot::named("x");

    // nested matcher: the guarded rewrite fires through the symmetry
    let mut eg: EGraph<Arith2> = EGraph::new(());
    let start = eg.add_expr(RecExpr::parse(term).unwrap());
    let a = eg.add_expr(RecExpr::parse(sym_a).unwrap());
    let b = eg.add_expr(RecExpr::parse(sym_b).unwrap());
    eg.union(&a, &b);
    let guard = move |subst: &Subst, _: &EGraph<Arith2>| !subst["e1"].slots().contains(&x);
    apply_rewrites(&mut eg, &[Rewrite::new_if("pull", lhs, rhs, guard)]);
    let goal_id = eg.add_expr(RecExpr::parse(goal).unwrap());
    assert!(eg.eq(&start, &goal_id));

    // multipattern matcher: the same rule flattened offers no reading the guard accepts
    let pat: MultiPattern<Arith2> = MultiPattern::parse("?p == (lam $x ?t), ?t == (f ?e1 ?e2)").unwrap();
    let (from, to) = (Pattern::PVar("p".to_string()), Pattern::parse(rhs).unwrap());
    let mut eg: EGraph<Arith2> = EGraph::new(());
    let start = eg.add_expr(RecExpr::parse(term).unwrap());
    let a = eg.add_expr(RecExpr::parse(sym_a).unwrap());
    let b = eg.add_expr(RecExpr::parse(sym_b).unwrap());
    eg.union(&a, &b);
    let matches = multi_ematch(&pat, &eg);
    let readings: Vec<&Subst> = matches.iter().filter(|s| !s["e1"].slots().contains(&x)).collect();
    assert!(!readings.is_empty(), "no reading puts the free variable first: {matches:?}");
    for s in readings {
        eg.union_instantiations(&from, &to, s, None);
    }
    let goal_id = eg.add_expr(RecExpr::parse(goal).unwrap());
    assert!(eg.eq(&start, &goal_id));
}

#[test]
// Rudi's `unify-redundant-and-symmetric-appid`: the body `?a` is shared under two binder
// chains, and its `f` class carries the swap symmetry, so the two chains' bound slots can be
// identified either way round. Written with pattern slots, `$x $y` against `$w $z` are rigid
// and nothing matches; the flexible `$?x` spelling stands for the bound variable itself and
// finds both pairings. `?x == (var $?x)` is how the right-hand side reads the bound variable.
fn multipat_flexible_bound_slots() {
    let mut eg: EGraph<Arith2> = EGraph::new(());
    eg.add_expr(RecExpr::parse("(f (lam $0 (lam $1 (f (var $0) (var $1)))) (lam $0 (lam $1 (f (var $0) (var $1)))))").unwrap());
    let a = eg.add_expr(RecExpr::parse("(f (var $0) (var $1))").unwrap());
    let b = eg.add_expr(RecExpr::parse("(f (var $1) (var $0))").unwrap());
    eg.union(&a, &b);

    let rigid: MultiPattern<Arith2> = MultiPattern::parse(
        "?out == (f ?l1 ?l2), ?l1 == (lam $x ?b1), ?b1 == (lam $y ?a), ?l2 == (lam $w ?b2), ?b2 == (lam $z ?a)",
    ).unwrap();
    assert_eq!(multi_ematch(&rigid, &eg).len(), 0, "pattern slots are rigid");

    let flexible: MultiPattern<Arith2> = MultiPattern::parse(
        "?out == (f ?l1 ?l2), ?l1 == (lam $?x ?b1), ?b1 == (lam $?y ?a), ?l2 == (lam $?w ?b2), ?b2 == (lam $?z ?a), ?x == (var $?x), ?w == (var $?w)",
    ).unwrap();
    assert!(flexible.to_string().contains("$?x"), "the spelling round-trips: {flexible}");
    // The `f` class's swap symmetry gives each pairing several spellings, so count the
    // pairings, not the matches.
    let matches = multi_ematch(&flexible, &eg);
    let same: Vec<bool> = matches.iter().map(|m| eg.eq(&m["x"], &m["w"])).collect();
    assert!(same.contains(&true) && same.contains(&false), "both pairings match: {matches:?}");
}
