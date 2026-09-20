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
    let matches = multi_ematch(&flexible, &eg);
    assert_eq!(matches.len(), 2, "{matches:?}");
    let same: Vec<bool> = matches.iter().map(|m| eg.eq(&m["x"], &m["w"])).collect();
    assert!(same.contains(&true) && same.contains(&false), "one match per pairing: {matches:?}");
}
