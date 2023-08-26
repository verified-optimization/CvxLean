use egg::{*};
use std::fs;
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

#[derive(Serialize, Debug)]
enum Direction {
    Forward, 
    Backward
}

#[derive(Serialize, Debug)]
pub struct Step {
    rewrite_name : String,
    direction : Direction,
    location : String,
    expected_term : String,
}

fn get_step_aux(term: &FlatTerm<Optimization>, location: &mut Option<String>, expected_term: &mut Option<String>) -> Option<Step> {
    match term.node {
        Optimization::ObjFun(_) => {
            *location = Some("objFun".to_string());

            let o_s = term.children[0].get_recexpr().to_string();
            *expected_term = Some(o_s);
        },
        Optimization::Constr([_, _]) => {
            let h_s = term.children[0].get_recexpr().to_string();
            *location = Some(h_s);

            let c_s = term.children[1].get_recexpr().to_string();
            *expected_term = Some(c_s);
        }
        _ => ()
    }

    if let Some(rule_name) = &term.backward_rule {
        if location.is_some() && expected_term.is_some() {
            return Some(Step {
                rewrite_name: rule_name.to_string(), 
                direction: Direction::Backward,
                location: location.clone().unwrap(),
                expected_term: expected_term.clone().unwrap(),
            });
        } else {
            return None;
        }
    }

    if let Some(rule_name) = &term.forward_rule {
        if location.is_some() && expected_term.is_some() {
            return Some(Step {
                rewrite_name: rule_name.to_string(), 
                direction: Direction::Forward,
                location: location.clone().unwrap(),
                expected_term: expected_term.clone().unwrap(),
            });
        } else {
            return None;
        }
    }

    if term.node.is_leaf() {
        return None
    } else {
        for child in &term.children {
            let child_res = 
                get_step_aux(child, location, expected_term);
            if child_res.is_some() {
                return child_res;
            }
        }
    };

    return None;
}

fn get_step(term: &FlatTerm<Optimization>) -> Option<Step> {
    return get_step_aux(term, &mut None, &mut None);
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

/// Return the rewrite steps if egg successfully found a chain of rewrites to
/// transform the term into DCP form. Return `None` if it didn't.
pub fn get_steps(prob: Minimization, domains: Vec<(String, Domain)>, debug: bool) -> Option<Vec<Step>> {
    let prob_s = prob.to_string();
    let expr: RecExpr<Optimization> = prob_s.parse().unwrap();
    
    let analysis = Meta {
        domains : domains.into_iter().collect()
    };

    let runner: Runner<Optimization, Meta> = 
        Runner::new(analysis)
        .with_explanations_enabled()
        .with_node_limit(1000)
        .with_iter_limit(3)
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
            match get_step(expl) {
                Some(step) => { res.push(step); }
                None => {}
            }
        }
    } else {
        return None;
    }

    return Some(res);
}
