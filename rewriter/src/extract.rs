use egg::{*};
use std::fs;
use serde::{Deserialize, Serialize};

use crate::domain;
use domain::Domain as Domain;

use crate::curvature;
use curvature::Curvature as Curvature;

use crate::optimization;
use optimization::Optimization as Optimizaiton;
use optimization::Meta as Meta;

use crate::rules;
use rules::rules as rules;

#[derive(Serialize, Debug)]
enum Direction {
    Forward, Backward
}

#[derive(Serialize, Debug)]
struct Step {
    rewrite_name : String,
    direction : Direction,
    expected_term : String,
}

fn get_rewrite_name_and_direction(term: &FlatTerm<Optimization>) -> Option<(String, Direction)> {
    if let Some(rule_name) = &term.backward_rule {
        return Some((rule_name.to_string(), Direction::Backward));
    }

    if let Some(rule_name) = &term.forward_rule {
        return Some((rule_name.to_string(), Direction::Forward));
    }

    if term.node.is_leaf() {
        return None
    } else {
        for child in &term.children {
            let child_res = 
                get_rewrite_name_and_direction(child);
            if child_res.is_some() {
                return child_res;
            }
        }
    };

    return None;
}

#[derive(Deserialize, Debug)]
pub struct Minimization {
    obj_fun : String,
    constrs : Vec<(String, String)>,
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

fn get_steps(prob: Minimization, domains: Vec<(String, Domain)>, debug: bool) -> Vec<Step> {
    let prob_s = prob.to_string();
    let expr: RecExpr<Optimization> = prob_s.parse().unwrap();
    
    let analysis = Meta {
        domains : domains.into_iter().collect()
    };

    let runner: Runner<Optimization, Meta> = 
        Runner::new(analysis)
        .with_explanations_enabled()
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
    
    let mut res = Vec::new();
    if best_cost.0 <= Curvature::Convex {
        for i in 0..flat_explanation.len() {
            let expl = &flat_explanation[i];
            let expected_term = expl.get_recexpr().to_string();
            match get_rewrite_name_and_direction(expl) {
                Some((rewrite_name, direction)) => {
                    res.push(Step { rewrite_name, direction, expected_term });
                }
                None => {}
            }
        }
    }

    return res;
}
