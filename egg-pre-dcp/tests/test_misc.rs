/*!
Miscellaneous tests that do not fit in any other category.
!*/

use egg_pre_dcp::domain;

use egg_pre_dcp::test_util::{*};

#[test]
fn test_norm2_with_one() {
    pre_dcp_check_expression_with_domain(
        "norm2_with_one",
        vec![("x", domain::free_dom())], 
        "(sqrt (add (pow (var x) 2) 1))");
}

#[test]
fn test_sqrt_pow4() {
    pre_dcp_check_expression_with_domain(
        "sqrt_pow4",
        vec![("x", domain::nonneg_dom())], 
        "(sqrt (pow (var x) 4))");
}

#[test]
fn test_div_constant_simp() {
    pre_dcp_check_expression(
        "div_constant_simp",
        "(div (div (var x) 20) (div 7 20))");
}

#[test]
fn test_div_constant_le_simp() {
    pre_dcp_check_expression_with_domain(
        "div_constant_le_simp",
        vec![("x", domain::nonneg_dom()), ("y", domain::pos_dom())], 
        "(le (div (qol 1 (var y)) 20) (mul (div 7 20) (sqrt (var x))))");
}
