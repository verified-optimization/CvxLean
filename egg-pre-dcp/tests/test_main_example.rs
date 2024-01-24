/*!
Test motivating example.
!*/

use egg_pre_dcp::domain;

use egg_pre_dcp::test_util::{*};

#[test]
fn test_main_example() {
    convexify_check_with_domain(
        vec![("x", domain::pos_dom())],
        "(var x)", 
        vec![
            "(le (div 1 (sqrt (var x))) (exp (var x)))"
        ]);
}
