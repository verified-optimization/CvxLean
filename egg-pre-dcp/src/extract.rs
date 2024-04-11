use egg::{*};
use std::convert::TryInto;
use std::fs;
use std::time::Duration;
use std::collections::HashMap;
use std::vec;
use std::time::Instant;
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

#[cfg(not(stop_on_success))]
use crate::cost;
#[cfg(not(stop_on_success))]
use cost::DCPCost as DCPCost;

use crate::explain_util;
use explain_util::Direction as Direction;
use explain_util::get_rewrite_name_and_direction as get_rewrite_name_and_direction;
use explain_util::expected_expr_with_hole as expected_expr_with_hole;

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

            let o_s = expected_expr_with_hole(&next.children[0]).get_string();
            *expected_term = Some(o_s);
        },
        Optimization::Constr([_, _]) => {
            let h_s = next.children[0].get_string();
            *location = Some(h_s);

            let c_s = expected_expr_with_hole(&next.children[1]).get_string();
            *expected_term = Some(c_s);
        }
        _ => {
            if expected_term.is_none() {
                // Out-of-context extraction. Useful for testing.
                let c_s = expected_expr_with_hole(&next).get_string();
                *expected_term = Some(c_s);
            }
        }
    }

    if let Some(rule_name) = &next.backward_rule {
        let subexpr_from = current.remove_rewrites().get_string();
        let subexpr_to = next.remove_rewrites().get_string();

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
        let subexpr_from = current.remove_rewrites().get_string();
        let subexpr_to = next.remove_rewrites().get_string();
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
#[allow(unused)]
pub fn get_steps_maybe_node_limit(prob: Minimization, domains_vec: Vec<(String, Domain)>, debug: bool, node_limit: Option<usize>) -> Option<Vec<Step>> {
    get_steps_from_string_maybe_node_limit(&prob.to_string(), domains_vec, debug, node_limit)
}

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
    let starting_time: Instant = Instant::now();
    let expr: RecExpr<Optimization> = prob_s.parse().unwrap();
    
    // Process domains, intersecting domains assigned to the same variable.
    let domains_len = domains_vec.len();
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
    
    // Choose the specified node limit, or select the default ones (for `stop_on_success`, we set
    // a large limit; note that if a DCP term is found it will not be reached).
    let node_limits = 
        if let Some(n) = node_limit { 
            vec![n] 
        } else { 
            if cfg!(stop_on_success) {
                vec![100000]
            } else {
                vec![2500, 5000, 10000, 20000, 40000, 80000] 
            }
        };

    for node_limit in node_limits  {
        let analysis = Meta {
            domains : domains.clone()
        };
        
        // Set up the runner with the given expression, analysis and limits.
        let iter_limit = node_limit / 250;
        let time_limit = (node_limit / 500).try_into().unwrap();
        let mut runner: Runner<Optimization, Meta> = 
            Runner::new(analysis)
            .with_explanations_enabled()
            .with_explanation_length_optimization()
            .with_node_limit(node_limit)
            .with_iter_limit(iter_limit)
            .with_time_limit(Duration::from_secs(time_limit))
            .with_expr(&expr);
        
            #[cfg(stop_on_success)]
            {
                runner = 
                    runner
                    .with_hook(|runner| {
                        let data = runner.egraph[runner.roots[0]].data.clone();
                        if data.curvature <= Curvature::Convex {
                            return Err("DCP term found.".to_string());
                        }
                        return Ok(());
                    })
                    .run(&rules())
            } 
            #[cfg(not(stop_on_success))]
            {
                runner = runner.run(&rules())
            }
        
        if debug {
            println!("Creating graph with {:?} nodes.", runner.egraph.total_number_of_nodes());
            let dot_str =  runner.egraph.dot().to_string();
            fs::write("test.dot", dot_str).expect("");
        }

        let root = runner.roots[0];

        // Extract the best term and best cost. This is obtained directly from the e-class 
        // analysis in the `stop_on_success` case, and by running the extractor otherwise.
        let best_curvature;
        let best_num_vars;
        let best_term_size;
        let best;
        #[cfg(stop_on_success)]
        {
            let result_data = runner.egraph[root].data.clone();
            best = result_data.best;
            best_curvature = result_data.curvature;
            best_num_vars = result_data.num_vars;
            best_term_size = result_data.term_size;
        }
        #[cfg(not(stop_on_success))] 
        {
            let cost_func = DCPCost { egraph: &runner.egraph };
            let extractor = Extractor::new(&runner.egraph, cost_func);
            let (best_cost_found, best_found) = extractor.find_best(root);
            best = best_found;
            best_curvature = best_cost_found.curvature;
            best_num_vars = best_cost_found.num_vars;
            best_term_size = best_cost_found.term_size;
        }

        let curvature = best_curvature;
        let num_vars = best_num_vars;

        // Note: each domain constraint is an expression with 3 nodes, e.g. `0 <= x`.
        let term_size = best_term_size + 3 * (domains_len as u32); 
        
        if curvature <= Curvature::Convex {
            if debug {
                let total_nodes = runner.egraph.total_number_of_nodes();
                println!("Succeeded with node limit {:?} (using {:?} nodes).", node_limit, total_nodes);
                println!("Best curvature: {:?}.", curvature);
                println!("Best number of variables: {:?}.", num_vars);
                println!("Best term size: {:?}.", term_size);
                println!("Best term: {:?}.", best.to_string());

                let build_time = starting_time.elapsed().as_millis();
                println!("E-graph building time: {:.2?} ms.", build_time);
                
                // Iterations data.
                let iterations = runner.iterations;
                let num_of_iterations = iterations.len() - 1;
                println!("Number of iterations: {:?}.", num_of_iterations);

                let mut num_rules_applied = 0;
                let mut num_iter = 0;
                for iteration in iterations {
                    let mut max_count = 0;
                    let mut max_rule = Symbol::from("");
                    for (name, count) in iteration.applied.iter() {
                        num_rules_applied += count;
                        if count.clone() > max_count {
                            max_count = count.clone();
                            max_rule = name.clone();
                        }
                    }
                    println!("--- Iteration {:?} data (cumulative) ---", num_iter);
                    println!("Rewrites applied: {:?}", num_rules_applied);
                    println!("E-nodes at start: {:?}", iteration.egraph_nodes);
                    println!("Max rule applied: {:?} (count: {:?}).", max_rule, max_count);
                    num_iter += 1;
                }
                println!("---");
                println!("Number of rules applied: {:?}.", num_rules_applied);
            }
        } else {
            // If term is not DCP, try with the next node limit.
            continue;
        }
        let after_build_time = Instant::now();

        // If term is DCP, find the explanation.
        let mut egraph = runner.egraph;
        let mut explanation : Explanation<Optimization> = 
            egraph.explain_equivalence(&expr, &best);
        let flat_explanation : &FlatExplanation<Optimization> =
            explanation.make_flat_explanation();
        if debug {
            println!("Number of steps: {}.", flat_explanation.len() - 1);
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

        if debug {
            let extract_time = after_build_time.elapsed().as_millis();
            let total_time = starting_time.elapsed().as_millis();
            println!("Step extraction time: {:.2?} ms.", extract_time);
            println!("Total time: {:.2?} ms.", total_time);
        }

        return Some(res);
    }

    // It failed for all node limits.
    return None;
}
