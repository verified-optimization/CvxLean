/*!
Tests for cost function minimization.
!*/

use egg_pre_dcp::test_util::{*};

#[test]
fn test_cost_function_number_of_variable_occurences() {
    pre_dcp_check(
        "cost_function_number_of_variable_occurences",
        "0",
        vec![
            "(le (var x) (sub 1 (var x)))"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_2() {
    pre_dcp_check(
        "cost_function_number_of_variable_occurences_2",
        "0",
        vec![
            "(le (add (mul 2 (var x)) (var x)) 0)"
        ]);
}
