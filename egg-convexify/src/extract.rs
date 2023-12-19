use egg::{*};
use std::convert::TryInto;
use std::fs;
use std::time::Duration;
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

use crate::domain;
use domain::Domain as Domain;

use crate::curvature;
use curvature::Curvature as Curvature;

use crate::optimization;
use optimization::Optimization as Optimization;
use optimization::Meta as Meta;

use crate::rules;
use rules::rules as rules;

use crate::explain_util;
use explain_util::Direction as Direction;
use explain_util::get_rewrite_name_and_direction as get_rewrite_name_and_direction;

#[derive(Serialize, Debug)]
pub struct Step {
    rewrite_name : String,
    direction : Direction,
    location : String,
    subexpr_from : String,
    subexpr_to : String,
    expected_term : String,
}

fn get_step_aux(
    direction: Direction,
    current: &FlatTerm<Optimization>,
    next: &FlatTerm<Optimization>,
    location: &mut Option<String>,
    expected_term: &mut Option<String>) ->
    Option<Step> {
    match next.node {
        Optimization::Prob(_) => { },
        Optimization::Constrs(_) => { },
        Optimization::ObjFun(_) => {
            *location = Some("objFun".to_string());

            let o_s = next.children[0].get_recexpr().to_string();
            *expected_term = Some(o_s);
        },
        Optimization::Constr([_, _]) => {
            let h_s = next.children[0].get_recexpr().to_string();
            *location = Some(h_s);

            let c_s = next.children[1].get_recexpr().to_string();
            *expected_term = Some(c_s);
        }
        _ => {
            if expected_term.is_none() {
                // Out-of-context extraction. Useful for testing.
                let c_s = next.get_recexpr().to_string();
                *expected_term = Some(c_s);
            }
        }
    }

    if let Some(rule_name) = &next.backward_rule {
        let subexpr_from = current.get_recexpr().to_string();
        let subexpr_to = next.get_recexpr().to_string();
        if expected_term.is_some() {
            return Some(Step {
                rewrite_name: rule_name.to_string(),
                direction: Direction::Backward,
                location: location.clone().unwrap_or_default(),
                subexpr_from: subexpr_from,
                subexpr_to: subexpr_to,
                expected_term: expected_term.clone().unwrap(),
            });
        } else {
            return None;
        }
    }

    if let Some(rule_name) = &next.forward_rule {
        let subexpr_from = current.get_recexpr().to_string();
        let subexpr_to = next.get_recexpr().to_string();
        if expected_term.is_some() {
            return Some(Step {
                rewrite_name: rule_name.to_string(),
                direction: Direction::Forward,
                location: location.clone().unwrap_or_default(),
                subexpr_from: subexpr_from,
                subexpr_to: subexpr_to,
                expected_term: expected_term.clone().unwrap(),
            });
        } else {
            return None;
        }
    }

    if next.node.is_leaf() {
        return None
    } else {
        let children = current.children.iter().zip(next.children.iter());
        for (left, right) in children {
            let child_res =
                get_step_aux(direction, left, right, location, expected_term);
            if child_res.is_some() {
                return child_res;
            }
        }
    };

    return None;
}

fn get_step(current: &FlatTerm<Optimization>, next: &FlatTerm<Optimization>) -> Option<Step> {
    if let Some((_rewrite_name, direction)) = get_rewrite_name_and_direction(next) {
        let location = &mut None;
        let expected_term = &mut None;
        return get_step_aux(direction, current, next, location, expected_term);
    }
    return None;
}

#[derive(Deserialize, Debug)]
pub struct Minimization {
    pub obj_fun : String,
    pub constrs : Vec<(String, String)>,
}

impl ToString for Minimization {
    fn to_string(&self) -> String {
        let obj_fun_s: String = format!("(objFun {})", self.obj_fun);
        let constrs_s_l : Vec<String> =
            self.constrs.iter().map(|(h, c)| format!("(constr {} {})", h, c)).collect();
        let constr_s = format!("(constrs {})", constrs_s_l.join(" "));
        return format!("(prob {} {})", obj_fun_s, constr_s);
    }
}

// Return the rewrite steps if egg successfully found a chain of rewrites to
// transform the term into DCP form. Return `None` if it didn't.
pub fn get_steps(prob: Minimization, domains_vec: Vec<(String, Domain)>, debug: bool) -> Option<Vec<Step>> {
    get_steps_from_string(&prob.to_string(), domains_vec, debug)
}

pub fn get_steps_from_string(prob_s: &str, domains_vec: Vec<(String, Domain)>, debug: bool) -> Option<Vec<Step>> {
    get_steps_from_string_maybe_node_limit(prob_s, domains_vec, debug, None)
}

pub fn get_steps_from_string_maybe_node_limit(
    prob_s: &str,
    domains_vec: Vec<(String, Domain)>,
    debug: bool,
    node_limit: Option<usize>) -> Option<Vec<Step>> {
    let expr: RecExpr<Optimization> = prob_s.parse().unwrap();

    // Process domains, intersecting domains assigned to the same variable.
    let mut domains: HashMap<String, Domain> = HashMap::new();
    for (x, dom) in domains_vec {
        if domains.contains_key(&x) {
            match domains.get_mut(&x) {
                Some(saved_dom) => {
                    *saved_dom = dom.intersection(saved_dom);
                }
                None => { }
            }
        } else {
            domains.insert(x, dom);
        }
    }
    for (_, d) in domains.clone() {
        if d.is_empty() {
            println!("Unfeasible problem.");
            return None;
        }
    }

    let analysis = Meta {
        domains : domains.clone()
    };

    let node_limit = node_limit.unwrap_or(100000);
    let iter_limit = node_limit / 250;
    let time_limit = (node_limit / 500).try_into().unwrap();

    let runner: Runner<Optimization, Meta> =
        Runner::new(analysis)
        .with_explanations_enabled()
        .with_explanation_length_optimization()
        .with_node_limit(node_limit)
        .with_iter_limit(iter_limit)
        .with_time_limit(Duration::from_secs(time_limit))
        .with_expr(&expr)
        .with_hook(|runner| {
            if runner.egraph[runner.roots[0]].data.curvature <= Curvature::Convex {
                return Err("DCP term found.".to_string());
            }
            return Ok(());
        })
        .run(&rules());

    if debug {
        println!("Creating graph with {:?} nodes.", runner.egraph.total_number_of_nodes());
        let dot_str =  runner.egraph.dot().to_string();
        fs::write("test.dot", dot_str).expect("");
    }

    let root = runner.roots[0];
    let result_data = runner.egraph[root].data.clone();
    let best = result_data.best;
    let curvature = result_data.curvature;
    if !(curvature <= Curvature::Convex) {
        return None;
    }
    if debug {
        println!("Best: {:?}", best.to_string());
        println!("Curvature: {:?}", curvature);
        println!("Num vars: {:?}", result_data.num_vars);
        println!("Term size: {:?}", result_data.term_size);
        runner.print_report();
    }

    let mut egraph = runner.egraph;
    let mut explanation : Explanation<Optimization> =
        egraph.explain_equivalence(&expr, &best);
    let flat_explanation : &FlatExplanation<Optimization> =
        explanation.make_flat_explanation();
    if debug {
        println!("{} steps", flat_explanation.len() - 1);
    }

    let mut res = Vec::new();
    for i in 0..flat_explanation.len() - 1 {
        let current = &flat_explanation[i];
        let next = &flat_explanation[i + 1];
        match get_step(current, next) {
            Some(step) => { res.push(step); }
            None => {
                // Should not get here.
                println!("Failed to extract step.");
            }
        }
    }

    return Some(res);
}
