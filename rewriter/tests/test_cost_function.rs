use egg_convexify::test_util::{*};

#[test]
fn test_cost_function_number_of_variable_occurences() {
    convexify_check(
        "0",
        vec![
            "(le (var x) (sub 1 (var x)))"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_2() {
    convexify_check(
        "0",
        vec![
            "(le (add (mul 2 (var x)) (var x)) 0)"
        ]);
}
