/*!
Tests from geometric programming.
!*/

use egg_pre_dcp::domain;

use egg_pre_dcp::test_util::{*};

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

#[test]
fn test_gp8() {
    convexify_check(
        "(mul (mul 2 (exp (var A))) (norm2 (exp (var w)) (exp (var h))))",
        vec![
            "(le (mul (div (mul 10 (norm2 (exp (var w)) (exp (var h)))) 2) (exp (var h))) (mul (div 1 2) (exp (var A))))",
            "(le (mul (div (mul 20 (norm2 (exp (var w)) (exp (var h)))) 2) (exp (var w))) (mul (div 1 2) (exp (var A))))",
            "(le 1 (exp (var h)))",
            "(le (exp (var h)) 100)",
            "(le 1 (exp (var w)))",
            "(le (exp (var w)) 100)", 
            "(le (mul (div 11 10) (exp (var r))) (sqrt (add (div (exp (var A)) (div 314159 50000)) (pow (exp (var r)) 2))))",
            "(le (sqrt (add (div (exp (var A)) (div 314159 50000)) (pow (exp (var r)) 2))) 10)"
    ]);
}
