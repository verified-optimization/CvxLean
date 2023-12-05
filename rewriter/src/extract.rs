use egg::{*};
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

use crate::cost;
use cost::DCPCost as DCPCost;

use crate::explain_utils;
use explain_utils::Direction as Direction;
use explain_utils::make_rule_table as make_rule_table;
use explain_utils::get_rewrite_name_and_direction as get_rewrite_name_and_direction;
use explain_utils::flat_term_check_rewrite_no_failure as flat_term_check_rewrite_no_failure;

pub type Rewrite = egg::Rewrite<Optimization, Meta>;

#[derive(Serialize, Debug)]
pub struct Step {
    rewrite_name : String,
    direction : Direction,
    location : String,
    // position : u32,
    expected_term : String,
}

fn get_step_aux(
    rewrite: &Rewrite,
    direction: Direction, 
    current: &FlatTerm<Optimization>, 
    next: &FlatTerm<Optimization>, 
    location: &mut Option<String>, 
    position : &mut u32, 
    expected_term: &mut Option<String>) -> 
    Option<Step> {
    match next.node {
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
        _ => ()
    }

    // Check if it matches to update the position.
    let matches = match direction {
        Direction::Forward => flat_term_check_rewrite_no_failure(current, next, rewrite),
        Direction::Backward => flat_term_check_rewrite_no_failure(next, current, rewrite),
    };
    if matches {
        *position += 1;
    }

    if let Some(rule_name) = &next.backward_rule {
        if location.is_some() && expected_term.is_some() {
            return Some(Step {
                rewrite_name: rule_name.to_string(), 
                direction: Direction::Backward,
                location: location.clone().unwrap(),
                // position: position.clone(),
                expected_term: expected_term.clone().unwrap(),
            });
        } else {
            return None;
        }
    }

    if let Some(rule_name) = &next.forward_rule {
        // let curr_s_t: String = current.get_recexpr().to_string();
        // let next_s_t = next.get_recexpr().to_string();
        // println!("curr {} : {}", rule_name, curr_s_t);
        // println!("next {} : {}", rule_name, next_s_t);
        if location.is_some() && expected_term.is_some() {
            return Some(Step {
                rewrite_name: rule_name.to_string(), 
                direction: Direction::Forward,
                location: location.clone().unwrap(),
                // position: position.clone(),
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
                get_step_aux(rewrite, direction, left, right, location, position, expected_term);
            if child_res.is_some() {
                return child_res;
            }
        }
    };

    return None;
}

fn get_step(rule_table: &HashMap<Symbol, &Rewrite>, current: &FlatTerm<Optimization>, next: &FlatTerm<Optimization>) -> Option<Step> {
    if let Some((rewrite_name, direction)) = get_rewrite_name_and_direction(next) {
        if let Some(rewrite) = rule_table.get(&rewrite_name) {
            let location = &mut None;
            let position = &mut 0;
            let expected_term = &mut None;
            return get_step_aux(rewrite, direction, current, next, location, position, expected_term);
        }
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

    for node_limit in [2500, 5000, 7500, 10000] {
        let analysis = Meta {
            domains : domains.clone()
        };
        
        let iter_limit = node_limit / 250;
        let runner: Runner<Optimization, Meta> = 
            Runner::new(analysis)
            .with_explanations_enabled()
            .with_node_limit(node_limit)
            .with_iter_limit(iter_limit)
            .with_time_limit(Duration::from_secs(5))
            .with_expr(&expr)
            .run(&rules());
        
        if debug {
            println!("Creating graph with {:?} nodes.", runner.egraph.total_number_of_nodes());
            let dot_str =  runner.egraph.dot().to_string();
            fs::write("test.dot", dot_str).expect("");
        }

        let root = runner.roots[0];

        let best_cost;
        let best;
        {
            let cost_func = DCPCost { egraph: &runner.egraph };
            let extractor = 
                Extractor::new(&runner.egraph, cost_func);
            let (best_cost_found, best_found) = 
                extractor.find_best(root);
            best = best_found;
            best_cost = best_cost_found;
        }
        if debug {
            println!("Best cost: {:?}", best_cost);
            println!("Best: {:?}", best.to_string());
        }

        let mut egraph = runner.egraph;
        let mut explanation : Explanation<Optimization> = 
            egraph.explain_equivalence(&expr, &best);
        let flat_explanation : &FlatExplanation<Optimization> =
            explanation.make_flat_explanation();
        
        let rules_copy = rules().clone();
        let rule_table = make_rule_table(&rules_copy);

        let mut res = Vec::new();
        if best_cost.0 <= Curvature::Convex {
            for i in 0..flat_explanation.len() - 1 {
                let current = &flat_explanation[i];
                let next = &flat_explanation[i + 1];
                match get_step(&rule_table, current, next) {
                    Some(step) => { res.push(step); }
                    None => { }
                }
            }
        } else {
            continue;
        }

        return Some(res);
    }

    // It failed for all node limits.
    return None;
}
