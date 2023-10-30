#[cfg(test)]
mod visualization {

use egg::{rewrite as rw, *};
use std::path::Path;
use std::time::Duration;
use std::fmt::Display;

use crate::domain; 
use domain::Domain as Domain;

use crate::optimization;
use optimization::Optimization as Optimization;
use optimization::Meta as Meta;
use optimization::is_gt_zero as is_gt_zero;


// Conversion to SVG.

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

fn egg_to_svg(s: &str, domains: Vec<(String, Domain)>, rules: &Vec<Rewrite<Optimization, Meta>>, filename: &str) {
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
        .run(rules);

    let serialized_egraph = egg_to_serialized_egraph(&runner.egraph);

    let path = Path::new("/Users/ramonfernandezmir/Documents/PhD-code/misc/egraph-serialize/tests")
        .join(filename)
        .with_extension("json");
    println!("Writing to {:?}", path);
    
    serialized_egraph.to_json_file(path).unwrap();
}


// Rules.

fn step0() -> Vec<Rewrite<Optimization, Meta>> { vec![] }

fn step1() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_gt_zero("?c")),
] }

fn step2() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_gt_zero("?c")),
    
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_gt_zero("?c")),
] }

fn step3() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_gt_zero("?c")),
    
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_gt_zero("?c")),
    
    rw!("exp_neg_eq_one_div-rev"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),
] }

fn step4() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_gt_zero("?c")),
    
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_gt_zero("?c")),
    
    rw!("exp_neg_eq_one_div-rev"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),

    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),
] }


// Run example.

#[test]
fn run() {
    let domains = vec![("x".to_string(), Domain::Pos)];
    let s = "(le (div 1 (sqrt (var x))) (exp (var x)))";
    let steps = vec![
        ("step0", step0()), 
        ("step1", step1()), 
        ("step2", step2()), 
        ("step3", step3()), 
        ("step4", step4())];
    for (filename, rules) in steps {
        egg_to_svg(s, domains.clone(), &rules, filename);
    }
}

}