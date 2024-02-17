/*!
Test motivating example.
!*/

mod test_main_example {

use egg_pre_dcp::domain;

use egg_pre_dcp::test_util::{*};

#[test]
fn test_main_example() {
    pre_dcp_check_with_domain_and_print(
        vec![("x", domain::pos_dom())],
        "(var x)", 
        vec![
            "(le (div 1 (sqrt (var x))) (exp (var x)))"
        ]);
}

}
