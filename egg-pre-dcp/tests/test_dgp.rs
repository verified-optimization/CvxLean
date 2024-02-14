/*!
Tests from geometric programming.
!*/

use egg_pre_dcp::domain;

use egg_pre_dcp::test_util::{*};

#[test]
fn test_gp1() {
    pre_dcp_check(
        "(exp (var u))",
        vec![
            "(le (pow (exp (var u)) 2) (div 10123 1000))"
        ]);
}

#[test]
fn test_gp2() {
    pre_dcp_check(
        "(exp (var u))",
        vec![
            "(le (mul (exp (var u)) (exp (var v))) (div 2691 500))"
        ]);
}

#[test]
fn test_gp3() {
    pre_dcp_check(
        "(exp (var u))",
        vec![
            "(le (sqrt (add (mul (exp (var u)) (exp (var u))) (exp (var v)))) 1)"
        ]);
}

#[test]
fn test_gp4() {
    pre_dcp_check(
        "(div 1 (div (exp (var u)) (exp (var v))))",
        vec![
            "(le 2 (exp (var u)))",
            "(le (exp (var u)) 3)",
            "(le (add (pow (exp (var u)) 2) (div (mul 3 (exp (var v))) (exp (var w)))) (sqrt (exp (var u))))",
            "(eq (div (exp (var u)) (exp (var v))) (pow (exp (var w)) 2))"
        ]);
}

#[test]
fn test_gp5() {
    pre_dcp_check(
        "(div 1 (div (exp (var u)) (exp (var v))))",
        vec![
            "(le 2 (exp (var u)))",
            "(le (exp (var u)) 3)",
            "(le (add (pow (exp (var u)) 2) (div (mul 3 (exp (var v))) (exp (var w)))) (sqrt (exp (var v))))",
            "(eq (div (exp (var u)) (exp (var v))) (pow (exp (var w)) 2))"
        ]);
}

#[test]
fn test_gp6() {
    pre_dcp_check(
        "(div 1 (div (exp (var u)) (exp (var v))))",
        vec![
            "(le 2 (exp (var u)))",
            "(le (exp (var u)) 3)",
            "(le (add (pow (exp (var u)) 2) (div (mul 3 (exp (var v))) (exp (var w)))) (mul 5 (sqrt (exp (var v))))",
            "(eq (mul (exp (var u)) (exp (var v))) (pow (exp (var w)) 2))"
        ]);
}

// 7
#[test]
fn test_gp7_with_params() {
    pre_dcp_check_with_domain(
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

{"request" : "PerformRewrite", "domains" : [], "target" : {"obj_fun" : "(div 1 (mul (mul (exp (var h')) (exp (var w'))) (exp (var d'))))", "constrs" : [["0:h4", "(le (mul 2 (add (mul (exp (var h')) (exp (var d'))) (mul (exp (var w')) (exp (var d'))))) 100)"], ["1:h5", "(le (mul (exp (var w')) (exp (var d'))) 10)"], ["2:h6", "(le (div 1 2) (div (exp (var h')) (exp (var w'))))"], ["3:h7", "(le (div (exp (var h')) (exp (var w'))) (div 1 2))"], ["4:h8", "(le 5 (div (exp (var d')) (exp (var w'))))"], ["5:h9", "(le (div (exp (var d')) (exp (var w'))) 6)"]]}}

// 8 
{"request" : "PerformRewrite", "domains" : [], "target" : {"obj_fun" : "(add (add (mul (mul (div 1 (exp (var u))) (div 1 (sqrt (exp (var v))))) (div 1 (exp (var w)))) (mul (mul (div 23 10) (exp (var u))) (exp (var w)))) (mul (mul (mul 4 (exp (var u))) (exp (var v))) (exp (var w))))", "constrs" : [["0:h4", "(le (add (mul (mul (div 1 3) (div 1 (pow (exp (var u)) 2))) (div 1 (pow (exp (var v)) 2))) (mul (mul (div 4 3) (sqrt (exp (var v)))) (div 1 (exp (var w))))) 1)"], ["1:h5", "(le (add (add (exp (var u)) (mul 2 (exp (var v)))) (mul 3 (exp (var w)))) 1)"], ["2:h6", "(eq (mul (mul (div 1 2) (exp (var u))) (exp (var v))) 1)"]]}}

// 9
#[test]
fn test_gp9() {
    pre_dcp_check(
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
{"request" : "PerformRewrite", "domains" : [], "target" : {"obj_fun" : "(mul (mul 2 (exp (var A'))) (norm2 (exp (var w')) (exp (var h'))))", "constrs" : [["0:h5", "(le (div (mul 10 (norm2 (exp (var w')) (exp (var h')))) (mul 2 (exp (var h')))) (mul (div 1 2) (exp (var A'))))"], ["1:h6", "(le (div (mul 20 (norm2 (exp (var w')) (exp (var h')))) (mul 2 (exp (var w')))) (mul (div 1 2) (exp (var A'))))"], ["2:h7", "(le 1 (exp (var h')))"], ["3:h8", "(le (exp (var h')) 100)"], ["4:h9", "(le 1 (exp (var w')))"], ["5:h10", "(le (exp (var w')) 100)"], ["6:h11", "(le (mul (div 11 10) (exp (var r'))) (sqrt (add (div (exp (var A')) (div 314159 50000)) (pow (exp (var r')) 2))))"], ["7:h12", "(le (sqrt (add (div (exp (var A')) (div 314159 50000)) (pow (exp (var r')) 2))) 10)"]]}}
