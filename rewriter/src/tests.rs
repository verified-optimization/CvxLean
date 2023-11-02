#[cfg(test)]
mod tests {

use crate::domain; 
use domain::Domain as Domain;

use crate::extract;
use extract::Minimization as Minimization;
use extract::get_steps as get_steps;

fn make(obj: &str, constrs: Vec<&str>) -> Minimization {
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

fn assert_steps_with_domain(domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>) {
    let prob = make(obj, constrs);
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), d.clone())).collect();
    let steps = get_steps(prob, domains, true);
    println!("{:?}", steps);
    assert!(steps.is_some());
}

fn assert_steps(obj: &str, constrs: Vec<&str>) {
    assert_steps_with_domain(vec![], obj, constrs);
}


// Examples.

#[test]
fn test_main_example() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())],
        "0", 
        vec![
            "(le (div 1 (sqrt (var x))) (exp (var x)))"
        ]);
    
}

#[test]
fn test_agp2() {
    // let r = domain::div(domain::pos_dom(), domain::nonneg_dom());
    // let r = domain::log(domain::pos_dom());
    // println!("{:?}", r);
    assert_steps(
        "(exp (var x))", 
        vec![
            "(le (mul (exp (var x)) (exp (var y))) (neg (div 2691 500)))"
        ]);
    
}

#[test]
fn test_gp3() {
    assert_steps(
        "(exp (var x))",
        vec![
            "(le (sqrt (add (mul (exp (var x)) (exp (var x))) (exp (var y)))) 1)"
        ]);
}

#[test]
fn test_gp4() {
    assert_steps(
        "(div 1 (div (exp (var x)) (exp (var y))))",
        vec![
            "(le 2 (exp (var x)))",
            // "(le (exp (var x)) 3)",
            // "(le (add (pow (exp (var x)) 2) (div (mul 3 (exp (var y))) (exp (var z)))) (sqrt (exp (var x))))",
            // "(eq (div (exp (var x)) (exp (var y))) (pow (exp (var z)) 2))"
        ]);
}

#[test]
fn test_gp6() {
    assert_steps_with_domain(
        vec![("Aflr", domain::pos_dom()), ("α", domain::pos_dom()), ("β", domain::pos_dom()), ("γ", domain::pos_dom()), ("δ", domain::pos_dom())],
        "(div 1 (mul (mul (exp (var h)) (exp (var w))) (exp (var d))))", 
        vec![
            "(le (mul 2 (add (mul (exp (var h)) (exp (var d))) (mul (exp (var w)) (exp (var d))))) (param Awall))",
            "(le (mul (exp (var w)) (exp (var d))) (param Aflr))",
            "(le (param α) (div (exp (var h)) (exp (var w))))",
            "(le (div (exp (var h)) (exp (var w))) (param β))",
            "(le (param γ) (div (exp (var d)) (exp (var w))))",
            "(le (div (exp (var d)) (exp (var w))) (param δ))"
        ]);
}


#[test]
fn test_dqcp() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())], 
        "(var x)", 
        vec![
            "(le (sqrt (div (var x) (add (var x) 1))) 1)"
        ]);
}

// Cost function.

#[test]
fn test_cost_function_number_of_variable_occurences() {
    assert_steps(
        "0",
        vec![
            "(le (var x) (sub 1 (var x)))"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_2() {
    assert_steps(
        "0",
        vec![
            "(le (add (mul 2 (var x)) (var x)) 0)"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_3() {
    assert_steps(
        "0",
        vec![
            "(le (add (mul 2 (var x)) (mul 3 (var x))) 0)"
        ]);
}

// Rule-based tests.

#[test]
fn test_log_le_log() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())],
        "0", 
        vec![
            "(le (log (var x)) (log (var y)))"
        ]);
}

#[test]
fn test_sub_iff_add_le() {
    assert_steps(
        "0", 
        vec![
            "(le (add 1 (var x)) (var x))",
        ])
}

#[test]
fn test_log_le_log_rev() {
    assert_steps(
        "0", 
        vec![
            "(le (exp (var x)) (exp (var y)))"
        ]);
}

#[test]
fn test_exp_add() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())],
        "0",
        vec![
            "(le (exp (add (log (var x)) 2)) 1)"
        ]);
}

#[test]
fn test_exp_neg_eq_one_div_rev() {
    assert_steps(
        "(div 1 (exp (var x)))",
        vec![
            "(le 1 (var x))"
        ]);
}

}
