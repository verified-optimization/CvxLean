/*!
Data collected for evaluation.
!*/

use serde::Serialize;

use crate::curvature;
use curvature::Curvature as Curvature;

#[derive(Serialize)]
pub struct IterationReport {
    // Number of rules applied at the iteration.
    num_rules_applied : u32,
    // E-nodes at the start of the iteration.
    num_nodes : u32,
    // Rule applied the most times.
    max_rule : String,
    max_rule_count : u32,
}

#[derive(Serialize)]
pub struct ComponentReport {
    // E-nodes data.
    nodes : u32,
    node_limit : u32,
    // Best term data.
    best_curvature : Curvature,
    best_num_vars : u32,
    best_term_size : u32,
    // Time to build the e-graph.
    build_time : u128,
    // Number of rules applied.
    num_rules_applied : u32,
    // Iteration data.
    num_iterations : u32,
    iterations : Vec<IterationReport>,
    // Time to get an explanation. 
    explain_time : u128,
    // Steps in the explanation.
    steps : u32,
}

#[derive(Serialize)]
pub struct Report {
    prob_name : String,
    // Main statistics.
    total_time : u128,
    total_nodes : u32,
    total_steps : u32,
    // Fine-grained components data.
    components : Vec<ComponentReport>,
}