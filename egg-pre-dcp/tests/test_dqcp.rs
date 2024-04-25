/*!
Tests from quasiconvex programming.
!*/

mod test_dqcp {

use egg_pre_dcp::domain;
use domain::Domain as Domain;

use egg_pre_dcp::test_util::{*};


#[test]
fn test_qcp1() {
    pre_dcp_check_with_domain_and_print(
        "qcp1",
        vec![("x", domain::pos_dom())], 
        "(var x)", 
        vec![
            "(le (sqrt (div (var x) (add (var x) 1))) 1)"
        ]);
}

#[test]
fn test_qcp2() {
    let d = Domain::make_oc(domain::zero(), domain::one());
    pre_dcp_check_with_domain_and_print(
        "qcp2",
        vec![("x", d)], 
        "(sqrt (sub (div 1 (pow (var x) 2)) 1))",
        vec![
            "(le (sub (mul (div 1 20) (div 1 (var x))) (mul (div 7 20) (sqrt (sub 1 (pow (var x) 2))))) 0)"
        ])
}

#[test]
fn test_qcp3() {
    let dx = Domain::make_singleton(12.0);
    let dy = Domain::make_cc(domain::make_float(0.001), domain::make_float(6.0));
    pre_dcp_check_with_domain_and_print(
        "qcp3",
        vec![("x", dx), ("y", dy)], 
        "0",
        vec![
            "(le (div (var x) (var y)) 3)"
        ])
}

#[test]
fn test_qcp4() {
    let dx = Domain::make_ci(domain::make_float(10.0));
    pre_dcp_check_with_domain_and_print(
        "qcp4",
        vec![("x", dx)], 
        "(neg (var x))",
        vec![
            "(le (div (sqrt (add (pow (add (var x) 1) 2) 4)) (sqrt (add (pow (var x) 2) 100))) 1)"
        ])
}

}

mod test_dqcp_other {

use egg_pre_dcp::domain;
use domain::Domain as Domain;

use egg_pre_dcp::test_util::{*};

#[test]
fn test_qcp2_with_params() {
    let dx = Domain::make_oc(domain::zero(), domain::one());
    let da = Domain::make_ci(domain::zero());
    let db = Domain::make_io(domain::one());
    pre_dcp_check_with_domain(
        "qcp2_with_params",
        vec![("x", dx), ("a", da), ("b", db)], 
        "(sqrt (sub (div 1 (pow (var x) 2)) 1))",
        vec![
            "(le (sub (mul (param a) (div 1 (var x))) (mul (sub 1 (param b)) (sqrt (sub 1 (pow (var x) 2))))) 0)"
        ])
}

}
