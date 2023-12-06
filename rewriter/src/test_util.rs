use crate::domain;
use domain::Domain as Domain;

use crate::extract;
use extract::Minimization as Minimization;
use extract::get_steps as get_steps;
use extract::get_steps_from_string as get_steps_from_string; 

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

fn convexify_check_with_domain_maybe_print(domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>, print: bool) {
    let prob = make(obj, constrs);
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), d.clone())).collect();
    let steps = get_steps(prob, domains, true);
    if steps.is_none() {
        panic!("Test failed, could not rewrite target into DCP form.");
    }
    if print {
        println!("{:?}", steps);
    }
}

pub fn convexify_check_with_domain(domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>) {
    convexify_check_with_domain_maybe_print(domains, obj, constrs, false)
}

pub fn convexify_check_with_domain_and_print(domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>) {
    convexify_check_with_domain_maybe_print(domains, obj, constrs, true)
}

pub fn convexify_check(obj: &str, constrs: Vec<&str>) {
    convexify_check_with_domain_maybe_print(vec![], obj, constrs, false)
}

pub fn convexify_check_and_print(obj: &str, constrs: Vec<&str>) {
    convexify_check_with_domain_maybe_print(vec![], obj, constrs, true)
}

// Used to test out-of-context expressions.

fn convexify_check_expression_with_domain_maybe_print(domains : Vec<(&str, Domain)>, s: &str, print: bool) {
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), d.clone())).collect();
    let steps = get_steps_from_string(s, domains, true);
    if steps.is_none() {
        panic!("Test failed, could not rewrite target into DCP form.");
    }
    if print {
        println!("{:?}", steps);
    }
}

pub fn convexify_check_expression_with_domain(domains : Vec<(&str, Domain)>,s: &str) {
    convexify_check_expression_with_domain_maybe_print(domains, s, false);
}

pub fn convexify_check_expression_with_domain_and_print(domains : Vec<(&str, Domain)>,s: &str) {
    convexify_check_expression_with_domain_maybe_print(domains, s, true);
}

pub fn convexify_check_expression(s: &str) {
    convexify_check_expression_with_domain_maybe_print(vec![], s, false);
}

pub fn convexify_check_expression_and_print(s: &str) {
    convexify_check_expression_with_domain_maybe_print(vec![], s, true);
}
