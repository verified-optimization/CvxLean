/*!
Tests for specific rewrite rules.
!*/

mod test_rules {

use egg_pre_dcp::domain;
use egg_pre_dcp::domain::Domain as Domain;

use egg_pre_dcp::test_util::{*};

#[test]
fn test_log_le_log() {
    pre_dcp_check_with_domain(
        "log_le_log",
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())],
        "0", 
        vec![
            "(le (log (var x)) (log (var y)))"
        ]);
}

#[test]
fn test_sub_iff_add_le() {
    pre_dcp_check(
        "sub_iff_add_le",
        "0", 
        vec![
            "(le (add 1 (var x)) (var x))",
        ])
}

#[test]
fn test_log_le_log_rev() {
    pre_dcp_check(
        "log_le_log_rev",
        "0", 
        vec![
            "(le (exp (var x)) (exp (var y)))"
        ]);
}

#[test]
fn test_exp_add() {
    pre_dcp_check_with_domain(
        "exp_add",
        vec![("x", domain::pos_dom())],
        "0",
        vec![
            "(le (exp (add (log (var x)) 2)) 1)"
        ]);
}

#[test]
fn test_exp_neg_eq_one_div_obj() {
    pre_dcp_check_with_domain(
        "exp_neg_eq_one_div_obj",
        vec![("x", Domain::make_ci(domain::one()))],
        "(mul (var x) (exp (neg (log (var x)))))",
        vec![
        ]);
}

#[test]
fn test_exp_neg_eq_one_div_constr() {
    pre_dcp_check_with_domain(
        "exp_neg_eq_one_div_constr",
        vec![("x", Domain::make_ci(domain::one()))],
        "(le (mul (var x) (exp (neg (log (var x))))) (var x))",
        vec![
        ]);
}

#[test]
fn test_log_mul_rev_constr() {
    pre_dcp_check_with_domain(
        "log_mul_rev_constr",
        vec![("x", domain::pos_dom())],
        "0",
        vec![
            "(le (exp (add (log (var x)) (log (add (var x) 1)))) 1)"
        ]);
}

#[test]
fn test_exp_neg_eq_one_div_rev() {
    pre_dcp_check(
        "exp_neg_eq_one_div_rev",
        "(div 1 (exp (var x)))",
        vec![
            "(le 1 (var x))"
        ]);
}

#[test]
fn test_div_self() {
    pre_dcp_check_with_domain(
        "div_self",
        vec![("x", domain::pos_dom())], 
        "0", 
        vec![
            "(le (mul (div (var x) (var x)) (var y)) 1)"
        ]);
}

#[test]
fn test_div_le_iff_rev() {
    pre_dcp_check_with_domain(
        "div_le_iff_rev",
        vec![("x", domain::pos_dom())], 
        "0", 
        vec![
            "(le (mul (var x) (var y)) (var x))"
        ]);
}

#[test]
fn test_log_div_rev_obj() {
    pre_dcp_check_with_domain(
        "log_div_rev_obj",
        vec![("x", domain::pos_dom())], 
        "(neg (sub (log (pow (var x) 2)) (log (var x))))", 
        vec![
        ]);
}

#[test]
fn test_geo_mean_fold() {
    pre_dcp_check_expression_with_domain(
        "geo_mean_fold",
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
        "(neg (sqrt (mul (var x) (var y))))");
}

#[test]
fn test_quad_over_lin_fold() {
    pre_dcp_check_expression_with_domain(
        "quad_over_lin_fold",
        vec![("x", domain::free_dom()), ("y", domain::pos_dom())], 
        "(div (pow (var x) 2) (var y))");
}

#[test]
fn test_norm2_fold() {
    pre_dcp_check_expression_with_domain(
        "norm2_fold",
        vec![("x", domain::free_dom()), ("y", domain::free_dom())], 
        "(sqrt (add (pow (var x) 2) (pow (var y) 2)))");
}

}
