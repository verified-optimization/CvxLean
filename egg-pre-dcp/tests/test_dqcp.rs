/*!
Tests from quasiconvex programming.
!*/

use egg_pre_dcp::domain;
use domain::Domain as Domain;

use egg_pre_dcp::test_util::{*};


#[test]
fn test_qcp1() {
    convexify_check_with_domain(
        vec![("x", domain::pos_dom())], 
        "(var x)", 
        vec![
            "(le (sqrt (div (var x) (add (var x) 1))) 1)"
        ]);
}

#[test]
fn test_qcp2() {
    let d = Domain::make_oc(domain::zero(), domain::one());
    convexify_check_with_domain(
        vec![("x", d)], 
        "(sqrt (sub (div 1 (pow (var x) 2)) 1))",
        vec![
            "(le (sub (mul (div 1 20) (div 1 (var x))) (mul (div 7 20) (sqrt (sub 1 (pow (var x) 2))))) 0)"
        ])
}

#[test]
fn test_qcp2_with_params() {
    let dx = Domain::make_oc(domain::zero(), domain::one());
    let da = Domain::make_ci(domain::zero());
    let db = Domain::make_io(domain::one());
    convexify_check_with_domain(
        vec![("x", dx), ("a", da), ("b", db)], 
        "(sqrt (sub (div 1 (pow (var x) 2)) 1))",
        vec![
            "(le (sub (mul (param a) (div 1 (var x))) (mul (sub 1 (param b)) (sqrt (sub 1 (pow (var x) 2))))) 0)"
        ])
}
