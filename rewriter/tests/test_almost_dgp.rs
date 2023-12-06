use egg_convexify::test_util::{*};

#[test]
fn test_agp2() {
    convexify_check(
        "(exp (var x))", 
        vec![
            "(le (mul (exp (var x)) (exp (var y))) (neg (div 2691 500)))"
        ]);
    
}
