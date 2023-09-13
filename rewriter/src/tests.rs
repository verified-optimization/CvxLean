#[cfg(test)]
mod tests {

use crate::domain; 
use domain::Domain as Domain;

use crate::extract;
use extract::Minimization as Minimization;
use extract::get_steps as get_steps;

fn make_basic(obj: &str, constrs: Vec<&str>) -> Minimization {
    let mut constrs_s = Vec::new();
    for i in 0..constrs.len() {
        let tag = format!("h{}", i);
        constrs_s.push((tag, constrs[i].to_string())); 
    }
    return Minimization {
        obj_fun : obj.to_string(),
        constrs : constrs_s,
    };
}

fn print_steps_with_domain(domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>) {
    let prob = make_basic(obj, constrs);
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), *d)).collect();
    let steps = get_steps(prob, domains, true);
    println!("{:?}", steps);
}

fn print_steps_basic(obj: &str, constrs: Vec<&str>) {
    print_steps_with_domain(vec![], obj, constrs);
}

// Examples.

#[test]
fn test_simple_example() {
    print_steps_with_domain(
        vec![("x", Domain::Pos)],
        "0", 
        vec![
            "(le (div 1 (sqrt (var x))) (exp (var x)))"
        ]);
}

#[test]
fn test_gp4() {
    print_steps_basic(
        "(div 1 (div (exp (var x)) (exp (var y))))",
        vec![
            "(le 2 (exp (var x)))",
            "(le (exp (var x)) 3)",
            "(le (add (pow (exp (var x)) 2) (div (mul 3 (exp (var y))) (exp (var z)))) (sqrt (exp (var x))))",
            "(eq (div (exp (var x)) (exp (var y))) (pow (exp (var z)) 2))"
        ]);
}

// Cost function.

#[test]
fn test_cost_function_number_of_variable_occurences() {
    print_steps_basic(
        "0",
        vec![
            "(le (var x) (sub 1 (var x)))"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_2() {
    print_steps_basic(
        "0",
        vec![
            "(le (add (mul 2 (var x)) (var x)) 0)"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_3() {
    print_steps_basic(
        "0",
        vec![
            "(le (add (mul 2 (var x)) (mul 3 (var x))) 0)"
        ]);
}

// Position. 

#[test]
fn test_position() {
    print_steps_basic(
        "0",
        vec![
            "(le (mul (mul 1 1) (mul 1 (mul 1 1))) 1)"
        ]);
}

#[test]
fn test_position_2() {
    print_steps_basic(
        "0",
        vec![
            "(le (add (var x) (add 1 (var x))) 1)"
        ]);
}

// Rule-based tests.

#[test]
fn test_log_le_log() {
    print_steps_basic(
        "0", 
        vec![
            "(le 1 (var x))",
            "(le 1 (var y))",
            "(le (log (var x)) (log (var y)))"
        ]);
}

#[test]
fn test_sub_iff_add_le() {
    print_steps_basic(
        "0", 
        vec![
            "(le (add 1 (var x)) (var x))",
        ])
}

#[test]
fn test_log_le_log_rev() {
    print_steps_basic(
        "0", 
        vec![
            "(le (exp (var x)) (exp (var y)))"
        ]);
}

#[test]
fn test_exp_add() {
    print_steps_with_domain(
        vec![("x", Domain::Pos)],
        "0",
        vec![
            "(le (exp (add (log (var x)) 2)) 1)"
        ]);
}

}
