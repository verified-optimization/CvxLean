/*!
Tests from geometric programming that do not follow the DGP rules strictly (often because of a 
negative sign that can be removed by rewritting the constraints appropriately).
!*/

mod test_almost_dgp {

use egg_pre_dcp::test_util::{*};

#[test]
fn test_agp1() {
    pre_dcp_check_and_print(
        "(exp (var u))",
        vec![
            "(le (sub (pow (exp (var u)) 2) (div 10123 1000)) 0)"
        ]);
}

#[test]
fn test_agp2() {
    pre_dcp_check_and_print(
        "(exp (var u))",
        vec![
            "(le (sub (mul (exp (var u)) (exp (var v))) (div 2691 500)) 0)"
        ]);
}

#[test]
fn test_agp3() {
    pre_dcp_check_and_print(
        "(add (add (exp (var u)) (exp (var v))) (exp (var w)))",
        vec![
            "(le 2 (exp (var u)))",
            "(le (exp (var u)) 3)",
            "(le (sqrt (exp (var u))) (sub (pow (exp (var u)) 2) (div (mul 6 (exp (var v))) (exp (var w)))))",
            "(eq (mul (exp (var u)) (exp (var v))) (exp (var w)))"
        ]);
}

#[test]
fn test_agp4() {
    pre_dcp_check_and_print(
        "(div 1 (mul (exp (var u)) (exp (var v))))",
        vec![
            "(le (mul (exp (var u)) (exp (var v))) (sub (sub 2 (exp (var u))) (exp (var v))))"
        ]);
}

}
