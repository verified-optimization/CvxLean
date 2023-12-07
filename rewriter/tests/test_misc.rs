/*!
Miscellaneous tests that do not fit in any other category.
!*/

use egg_convexify::domain;

use egg_convexify::test_util::{*};

#[test]
fn test_norm2_with_one() {
    convexify_check_expression_with_domain(
        vec![("x", domain::free_dom())], 
        "(sqrt (add (pow (var x) 2) 1))");
}

#[test]
fn test_sqrt_pow4() {
    convexify_check_expression_with_domain(
        vec![("x", domain::nonneg_dom())], 
        "(sqrt (pow (var x) 4))");
}
