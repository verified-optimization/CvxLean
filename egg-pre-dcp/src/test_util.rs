use crate::domain;
use domain::Domain as Domain;

use crate::explain_util;
use explain_util::Minimization as Minimization;
use explain_util::MinimizationOrExpr as MinimizationOrExpr;

use crate::extract;
use extract::get_steps as get_steps;
use extract::get_steps_maybe_node_limit as get_steps_maybe_node_limit;
use extract::get_steps_from_string_maybe_node_limit as get_steps_from_string_maybe_node_limit; 

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

fn pre_dcp_check_with_domain_maybe_print(
        prob_name : &str, 
        domains : Vec<(&str, Domain)>, 
        obj: &str, 
        constrs: Vec<&str>, 
        print: bool) {
    let prob = make(obj, constrs);
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), d.clone())).collect();
    let steps = 
        match std::env::var("EGG_PRE_DCP_NODE_LIMIT") {
            Result::Ok(v) => { 
                let node_limit = v.parse::<usize>().unwrap();
                get_steps_maybe_node_limit(prob_name, prob, domains, print, Some(node_limit)) 
            }
            Result::Err(_) => { 
                get_steps(prob_name, prob, domains, print)
            }
        };
    if steps.is_none() {
        panic!("Test failed, could not rewrite target into DCP form.");
    }
    if print {
        println!("{:?}", steps);
    }
}

pub fn pre_dcp_check_with_domain(
        prob_name : &str, domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>) {
    pre_dcp_check_with_domain_maybe_print(prob_name, domains, obj, constrs, false)
}

pub fn pre_dcp_check_with_domain_and_print(
        prob_name : &str, domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>) {
    pre_dcp_check_with_domain_maybe_print(prob_name, domains, obj, constrs, true)
}

pub fn pre_dcp_check(prob_name : &str, obj: &str, constrs: Vec<&str>) {
    pre_dcp_check_with_domain_maybe_print(prob_name, vec![], obj, constrs, false)
}

pub fn pre_dcp_check_and_print(prob_name : &str, obj: &str, constrs: Vec<&str>) {
    pre_dcp_check_with_domain_maybe_print(prob_name, vec![], obj, constrs, true)
}

// Used to test out-of-context expressions.

fn pre_dcp_check_expression_with_domain_maybe_print_maybe_node_limit(
        prob_name : &str, 
        domains : Vec<(&str, Domain)>, 
        prob_s: &str, 
        print: bool, 
        node_limit: Option<usize>) {
    // NOTE: Even if the node limit is passed as an argument, the environment variable is used if it 
    // is set, hence overriding the argument.
    let node_limit = 
    match std::env::var("EGG_PRE_DCP_NODE_LIMIT") {
        Result::Ok(v) => { 
            let node_limit = v.parse::<usize>().unwrap();
            Some(node_limit) 
        }
        Result::Err(_) => { 
            node_limit
        }
    };
    let expr = MinimizationOrExpr::Expr(prob_s.to_string());
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), d.clone())).collect();
    let steps = get_steps_from_string_maybe_node_limit(prob_name, expr, domains, true, node_limit);
    if steps.is_none() {
        panic!("Test failed, could not rewrite target into DCP form.");
    }
    if print {
        println!("{:?}", steps);
    }
}

fn pre_dcp_check_expression_with_domain_maybe_print(
        prob_name: &str, domains: Vec<(&str, Domain)>, s: &str, print: bool) {
    pre_dcp_check_expression_with_domain_maybe_print_maybe_node_limit(
        prob_name, domains, s, print, None);
}

pub fn pre_dcp_check_expression_with_domain(
        prob_name: &str, domains: Vec<(&str, Domain)>,s: &str) {
    pre_dcp_check_expression_with_domain_maybe_print(prob_name, domains, s, false);
}

pub fn pre_dcp_check_expression_with_domain_and_print(
        prob_name: &str, domains: Vec<(&str, Domain)>,s: &str) {
    pre_dcp_check_expression_with_domain_maybe_print(prob_name, domains, s, true);
}

fn pre_dcp_check_expression_with_domain_and_node_limit_maybe_print(
        prob_name: &str, domains: Vec<(&str, Domain)>, s: &str, print: bool, node_limit: usize) {
    pre_dcp_check_expression_with_domain_maybe_print_maybe_node_limit(
        prob_name, domains, s, print, Some(node_limit));
}

pub fn pre_dcp_check_expression_with_domain_and_node_limit(
        prob_name: &str, domains: Vec<(&str, Domain)>, s: &str, node_limit: usize) {
    pre_dcp_check_expression_with_domain_and_node_limit_maybe_print(
        prob_name, domains, s, false, node_limit);
}

pub fn pre_dcp_check_expression_with_domain_and_node_limit_and_print(
        prob_name: &str, domains: Vec<(&str, Domain)>, s: &str, node_limit: usize) {
    pre_dcp_check_expression_with_domain_and_node_limit_maybe_print(
        prob_name, domains, s, true, node_limit);
}

pub fn pre_dcp_check_expression(prob_name: &str, s: &str) {
    pre_dcp_check_expression_with_domain_maybe_print(prob_name, vec![], s, false);
}

pub fn pre_dcp_check_expression_and_print(prob_name: &str, s: &str) {
    pre_dcp_check_expression_with_domain_maybe_print(prob_name, vec![], s, true);
}
