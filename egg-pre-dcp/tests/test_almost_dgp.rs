/*!
Tests from geometric programming that do not follow the DGP rules.
!*/

use egg_pre_dcp::test_util::{*};

#[test]
fn test_agp2() {
    pre_dcp_check(
        "(exp (var x))", 
        vec![
            "(le (sub (mul (exp (var x)) (exp (var y))) (div 2691 500)) 0)"
        ]);
}
