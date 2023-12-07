/*!
Tests from geometric programming.
!*/

use egg_convexify::domain;

use egg_convexify::test_util::{*};

#[test]
fn test_gp3() {
    convexify_check(
        "(exp (var x))",
        vec![
            "(le (sqrt (add (mul (exp (var x)) (exp (var x))) (exp (var y)))) 1)"
        ]);
}

#[test]
fn test_gp4() {
    convexify_check(
        "(div 1 (div (exp (var x)) (exp (var y))))",
        vec![
            "(le 2 (exp (var x)))",
            "(le (exp (var x)) 3)",
            "(le (add (pow (exp (var x)) 2) (div (mul 3 (exp (var y))) (exp (var z)))) (sqrt (exp (var x))))",
            "(eq (div (exp (var x)) (exp (var y))) (pow (exp (var z)) 2))"
        ]);
}

#[test]
fn test_gp6() {
    convexify_check_with_domain(
        vec![
            ("Aflr", domain::pos_dom()), 
            ("α"   , domain::pos_dom()), 
            ("β"   , domain::pos_dom()), 
            ("γ"   , domain::pos_dom()), 
            ("δ"   , domain::pos_dom())],
        "(div 1 (mul (mul (exp (var h)) (exp (var w))) (exp (var d))))", 
        vec![
            "(le (mul 2 (add (mul (exp (var h)) (exp (var d))) (mul (exp (var w)) (exp (var d))))) (param Awall))",
            "(le (mul (exp (var w)) (exp (var d))) (param Aflr))",
            "(le (param α) (div (exp (var h)) (exp (var w))))",
            "(le (div (exp (var h)) (exp (var w))) (param β))",
            "(le (param γ) (div (exp (var d)) (exp (var w))))",
            "(le (div (exp (var d)) (exp (var w))) (param δ))"
        ]);
}
