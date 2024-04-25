/*!
Data collected for evaluation.
!*/

use serde::Serialize;

use crate::curvature;
use curvature::Curvature as Curvature;

use crate::explain_util;
use crate::explain_util::Minimization as Minimization;
use explain_util::MinimizationOrExpr as MinimizationOrExpr;

#[derive(Debug, Serialize)]
pub struct IterationReport {
    // Number of rules applied up to this iteration.
    num_rules_applied : usize,
    // E-nodes at the start of the iteration. Note that the number of nodes at the last iteration is 
    // *not* the total number of nodes in the e-graph. Moreover, this number is not exact, as it is 
    // the size of the hashcons map, so it should be regarded as a conservative estimate.
    num_nodes : usize,
    // Rule applied the most times.
    max_rule : String,
    max_rule_count : usize,
}

impl IterationReport {
    pub fn new(
            num_rules_applied: usize, 
            num_nodes: usize, 
            max_rule: String, 
            max_rule_count: usize) -> Self {
        IterationReport {
            num_rules_applied,
            num_nodes,
            max_rule,
            max_rule_count,
        }
    }
}

#[derive(Debug, Serialize)]
pub struct ComponentReport {
    // Component name: objFun, expr, h1, h2, ...
    component_name : String,
    // E-nodes data.
    nodes : usize,
    node_limit : usize,
    // Best term data.
    best_curvature : Curvature,
    best_num_vars : u32,
    best_term_size : u32,
    best_term: String,
    // Time to build the e-graph.
    build_time : u128,
    // Iteration data.
    num_iterations : usize,
    iteration_reports : Vec<IterationReport>,
    // Number of rules applied.
    num_rules_applied : usize,
    // Number of steps in the explanation.
    steps_count : usize,
    // Time to get an explanation. 
    explain_time : u128,
    // Component time.
    component_time : u128,
}

impl ComponentReport {
    pub fn new(component_name: String) -> Self {
        ComponentReport {
            component_name,
            nodes: 0,
            node_limit: 0,
            best_curvature: Curvature::Unknown,
            best_num_vars: 0,
            best_term_size: 0,
            best_term: String::new(),
            build_time: 0,
            num_iterations: 0,
            iteration_reports: Vec::new(),
            num_rules_applied: 0,
            steps_count: 0,
            explain_time: 0,
            component_time: 0,
        }
    }

    pub fn set_nodes(&mut self, nodes: usize) {
        self.nodes = nodes;
    }

    pub fn set_node_limit(&mut self, node_limit: usize) {
        self.node_limit = node_limit;
    }

    pub fn set_best_curvature(&mut self, best_curvature: Curvature) {
        self.best_curvature = best_curvature;
    }

    pub fn set_best_num_vars(&mut self, best_num_vars: u32) {
        self.best_num_vars = best_num_vars;
    }

    pub fn set_best_term_size(&mut self, best_term_size: u32) {
        self.best_term_size = best_term_size;
    }

    pub fn set_best_term(&mut self, best_term: String) {
        self.best_term = best_term;
    }

    pub fn set_build_time(&mut self, build_time: u128) {
        self.build_time = build_time;
    }

    pub fn set_num_iterations(&mut self, num_iterations: usize) {
        self.num_iterations = num_iterations;
    }

    pub fn add_iteration_report(&mut self, iteration_report: IterationReport) {
        self.iteration_reports.push(iteration_report);
    }

    pub fn set_num_rules_applied(&mut self, num_rules_applied: usize) {
        self.num_rules_applied = num_rules_applied;
    }

    pub fn set_steps_count(&mut self, steps_count: usize) {
        self.steps_count = steps_count;
    }

    pub fn set_explain_time(&mut self, explain_time: u128) {
        self.explain_time = explain_time;
    }

    pub fn set_component_time(&mut self, component_time: u128) {
        self.component_time = component_time;
    }
}

#[derive(Debug, Serialize)]
pub struct Report {
    prob_name : String,
    // Main statistics.
    total_time : u128,
    total_nodes : usize,
    total_steps : usize,
    // Best term data.
    best_curvature : Curvature,
    best_num_vars : u32,
    best_term_size : u32,
    best_term : MinimizationOrExpr,
    // Fine-grained components data.
    component_reports : Vec<ComponentReport>,
}

impl Report {
    pub fn new(prob_name: String) -> Self {
        Report {
            prob_name,
            total_time: 0,
            total_nodes: 0,
            total_steps: 0,
            best_curvature: Curvature::Unknown,
            best_num_vars: 0,
            best_term_size: 0,
            best_term: MinimizationOrExpr::Expr(String::new()),
            component_reports: Vec::new(),
        }
    }

    pub fn set_total_time(&mut self, total_time: u128) {
        self.total_time = total_time;
    }

    pub fn set_initial_term_size(&mut self, term_size: u32) {
        self.best_term_size = term_size;
    }

    pub fn add_component_report(&mut self, component_report: ComponentReport) {
        self.total_nodes += component_report.nodes;
        self.total_steps += component_report.steps_count;

        // The curvatures of the components are assumed to be <= Convex. We take the maximum.
        if self.best_curvature == Curvature::Unknown || 
           component_report.best_curvature > self.best_curvature {
            self.best_curvature = component_report.best_curvature.clone();
        } 

        // Number of vars and term size are just summed.
        self.best_num_vars += component_report.best_num_vars;
        self.best_term_size += component_report.best_term_size;

        // A little more work is needed to place the best term from the component / expression into 
        // the best term of the report.
        if component_report.component_name.eq("expr") {
            self.best_term = MinimizationOrExpr::Expr(component_report.best_term.clone());
        } else if component_report.component_name.eq("objFun") {
            match &mut self.best_term {
                MinimizationOrExpr::Expr(_) => {
                    let obj_fun = component_report.best_term.clone();
                    let min = Minimization { obj_fun, constrs: Vec::new() };
                    self.best_term = MinimizationOrExpr::Min(min);
                },
                MinimizationOrExpr::Min(min) => {
                    min.obj_fun = component_report.best_term.clone();
                },
            }
        } else {
            match &mut self.best_term {
                MinimizationOrExpr::Expr(_) => {
                    panic!("Minimization expected.");
                },
                MinimizationOrExpr::Min(min) => {
                    let constr_name = component_report.component_name.clone();
                    let constr_s = component_report.best_term.clone();
                    min.constrs.push((constr_name, constr_s));
                },
                
            }
        }

        self.component_reports.push(component_report);
    }
}
