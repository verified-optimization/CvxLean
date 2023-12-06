use egg_convexify::domain;

use egg_convexify::test_util::{*};


#[test]
fn test_dqcp() {
    convexify_check_with_domain(
        vec![("x", domain::pos_dom())], 
        "(var x)", 
        vec![
            "(le (sqrt (div (var x) (add (var x) 1))) 1)"
        ]);
}
