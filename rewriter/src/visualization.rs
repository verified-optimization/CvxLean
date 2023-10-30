#[cfg(test)]
mod visualization {

use egg::{*};
use std::path::Path;
use std::time::Duration;
use std::collections::HashMap;
use std::fmt::Display;

use crate::domain; 
use domain::Domain as Domain;

use crate::optimization;
use optimization::Optimization as Optimization;
use optimization::Meta as Meta;

use crate::rules;
use rules::rules as rules;

pub fn egg_to_serialized_egraph<L, A>(egraph: &EGraph<L, A>) -> egraph_serialize::EGraph
where
    L: Language + Display,
    A: Analysis<L>,
{
    use egraph_serialize::*;    
    let mut out = EGraph::default();
    for class in egraph.classes() {
        for (i, node) in class.nodes.iter().enumerate() {
            out.add_node(
                format!("{}.{}", class.id, i),
                Node {
                    op: node.to_string(),
                    children: node
                        .children()
                        .iter()
                        .map(|id| NodeId::from(format!("{}.0", id)))
                        .collect(),
                    eclass: ClassId::from(format!("{}", class.id)),
                    cost: Cost::new(1.0).unwrap(),
                },
            )
        }
    }
    out
}

fn egg_to_svg(s: &str, domains: Vec<(String, Domain)>) {
    let analysis = Meta {
        domains : domains.clone().into_iter().collect()
    };
    let expr: RecExpr<Optimization> = s.parse().unwrap();
    let runner: Runner<Optimization, Meta> = 
        Runner::new(analysis)
        .with_explanations_enabled()
        .with_node_limit(1000)
        .with_iter_limit(4)
        .with_time_limit(Duration::from_secs(5))
        .with_expr(&expr)
        .run(&rules::rules_for_visualization());

    let serialized_egraph = egg_to_serialized_egraph(&runner.egraph);

    let path = Path::new("/Users/ramonfernandezmir/Documents/PhD-code/misc/egraph-serialize/tests")
        .join("test")
        .with_extension("json");
    println!("Writing to {:?}", path);
    
    serialized_egraph.to_json_file(path).unwrap();
}

// Examples.

#[test]
fn test_main_example() {
    let domains = vec![("x".to_string(), Domain::Pos)];
    let s = "(le (div 1 (sqrt (var x))) (exp (var x)))";
    egg_to_svg(s, domains);
}

}