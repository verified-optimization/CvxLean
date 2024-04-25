use egg::{*};
use std::convert::TryInto;
use std::fs;
use std::time::Duration;
use std::collections::HashMap;
use std::vec;
use std::time::Instant;
use serde::Serialize;

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
use explain_util::Minimization as Minimization;
use explain_util::MinimizationOrExpr as MinimizationOrExpr;
use explain_util::Direction as Direction;
use explain_util::get_rewrite_name_and_direction as get_rewrite_name_and_direction;
use explain_util::expected_expr_with_hole as expected_expr_with_hole;

use crate::report;
use report::IterationReport as IterationReport;
use report::ComponentReport as ComponentReport;
use report::Report as Report;

// A step in the explanation, and methods from extracting them from pairs of "flat terms".

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

// Return the rewrite steps if egg successfully found a chain of rewrites to transform the term into
// DCP form. Return `None` if it didn't.

#[allow(unused)]
pub fn get_steps_maybe_node_limit(
        prob_name : &str, 
        prob: Minimization, 
        domains_vec: Vec<(String, Domain)>, 
        debug: bool, 
        node_limit: Option<usize>) -> Option<HashMap<String, Vec<Step>>>  {
    get_steps_from_string_maybe_node_limit(
        prob_name, MinimizationOrExpr::Min(prob), domains_vec, debug, node_limit)
}

pub fn get_steps(
        prob_name : &str, 
        prob: Minimization, 
        domains_vec: Vec<(String, Domain)>, 
        debug: bool) -> Option<HashMap<String, Vec<Step>>> {
    get_steps_from_string_maybe_node_limit(
        prob_name, MinimizationOrExpr::Min(prob), domains_vec, debug, None)
}

pub fn get_steps_from_string_maybe_node_limit(
        prob_name : &str, 
        prob: MinimizationOrExpr, 
        domains_vec: Vec<(String, Domain)>, 
        debug: bool, 
        node_limit: Option<usize>) -> Option<HashMap<String, Vec<Step>>> {
    let starting_time = Instant::now();
    let mut report = Report::new(prob_name.to_string());
    let mut res = HashMap::new();
    
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

    // NOTE: each domain constraint is an expression with 3 nodes, e.g. `0 <= x`.
    report.set_initial_term_size(3 * (domains_len as u32));

    // Go through the components. 
    // TODO: Opportunity to parallelize this loop (e.g., using rayon).
    for (component_name, component_s) in prob.iter() {
        let component_starting_time = Instant::now();

        // Expression to rewrite.
        let expr: RecExpr<Optimization> = component_s.parse().unwrap();
        
        // Choose the specified node limit, or select the default ones (for `stop_on_success`, we 
        // set a large limit; note that if a DCP term is found it will not be reached).
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
        let mut success = false;

        for node_limit in node_limits  {
            let mut component_report = ComponentReport::new(component_name.clone());

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
            
            if best_curvature <= Curvature::Convex {
                let nodes = runner.egraph.total_number_of_nodes();
                let build_time = starting_time.elapsed().as_millis();

                component_report.set_nodes(nodes);
                component_report.set_node_limit(node_limit);
                component_report.set_best_curvature(best_curvature);
                component_report.set_best_num_vars(best_num_vars);
                component_report.set_best_term_size(best_term_size);
                component_report.set_best_term(best.to_string());
                component_report.set_build_time(build_time);
                
                // Iterations data.
                let iterations = runner.iterations;
                let num_of_iterations = iterations.len() - 1;
                component_report.set_num_iterations(num_of_iterations);

                let mut num_rules_applied = 0;
                for i in 0..num_of_iterations  {
                    let iteration = &iterations[i];
                    let mut max_count = 0;
                    let mut max_rule = Symbol::from("");
                    for (name, count) in iteration.applied.iter() {
                        num_rules_applied += count;
                        if count.clone() > max_count {
                            max_count = count.clone();
                            max_rule = name.clone();
                        }
                    }

                    let iter_report = IterationReport::new(
                        num_rules_applied,
                        iteration.egraph_nodes,
                        max_rule.to_string(),
                        max_count,
                    );
                    component_report.add_iteration_report(iter_report);
                }
                component_report.set_num_rules_applied(num_rules_applied);
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
            component_report.set_steps_count(flat_explanation.len() - 1);

            let mut steps = Vec::new();
            for i in 0..flat_explanation.len() - 1 {
                let current = &flat_explanation[i];
                let next = &flat_explanation[i + 1];
                match get_step(current, next) {
                    Some(mut step) => {
                        // TODO: `get_step_aux` can be simplified, since we know the location 
                        // directly.
                        step.location = component_name.clone();
                        steps.push(step); 
                    }
                    None => {
                        panic!("Failed to extract step.");
                    }
                }
            }

            let explain_time = after_build_time.elapsed().as_millis();
            let component_time = component_starting_time.elapsed().as_millis();
            component_report.set_explain_time(explain_time);
            component_report.set_component_time(component_time);

            report.add_component_report(component_report);

            res.insert(component_name.clone(), steps);

            success = true;
            break;
        }

        // It failed for all node limits.
        if !success {
            return None;
        }
    }

    // Craft final report.
    let total_time = starting_time.elapsed().as_millis();
    report.set_total_time(total_time);

    if debug {
        println!("{:?}", report);
    }

    return Some(res);
}
