use egg::{*};
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

use crate::optimization;
use optimization::Optimization as Optimization;
use optimization::Meta as Meta;

pub type Rewrite = egg::Rewrite<Optimization, Meta>;

// Representation of an optimization problem by its components.

#[derive(Deserialize, Debug)]
pub struct Minimization {
    pub obj_fun : String,
    pub constrs : Vec<(String, String)>,
}

impl ToString for Minimization {
    fn to_string(&self) -> String {
        let obj_fun_s: String = format!("(objFun {})", self.obj_fun);
        let constrs_s_l : Vec<String> = 
            self.constrs.iter().map(
                |(h, c)| format!("(constr {} {})", h, c)).collect();
        let constr_s = format!("(constrs {})", constrs_s_l.join(" "));
        return format!("(prob {} {})", obj_fun_s, constr_s);
    }
}

impl Serialize for Minimization {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
        serializer.serialize_str(&self.to_string())
    }
}

pub struct MinimizationIter {
    min_iter : Vec<(String, String)>,
}

impl Minimization {
    pub fn iter(&self) -> MinimizationIter {
        let obj_fun_s = format!("(objFun {})", self.obj_fun);
        let mut min_iter = vec![("objFun".to_string(), obj_fun_s.clone())];
        min_iter.append(&mut self.constrs.clone());
        MinimizationIter { min_iter }
    }
}

impl Iterator for MinimizationIter {
    type Item = (String, String);

    fn next(&mut self) -> Option<Self::Item> {
        if self.min_iter.is_empty() {
            None
        } else {
            Some(self.min_iter.remove(0))
        }
    }
}

// Since sometimes we want to rewrite a full optimization problem, and sometimes just an expression.
#[derive(Deserialize, Debug)]
pub enum MinimizationOrExpr {
    Min(Minimization),
    Expr(String),
}

impl Serialize for MinimizationOrExpr {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
        match self {
            MinimizationOrExpr::Min(min) => min.serialize(serializer),
            MinimizationOrExpr::Expr(expr) => expr.serialize(serializer),
        }
    }
}

impl MinimizationOrExpr {
    pub fn iter(&self) -> MinimizationIter {
        match self {
            MinimizationOrExpr::Min(min) => min.iter(),
            MinimizationOrExpr::Expr(expr) => {
                let min_iter = vec![("expr".to_string(), expr.clone())];
                MinimizationIter { min_iter }
            }
        }
    }
}

// Reading flat terms.

#[derive(Clone, Copy, Serialize, Debug)]
pub enum Direction {
    Forward, 
    Backward
}

pub fn get_rewrite_name_and_direction(t : &FlatTerm<Optimization>) -> Option<(Symbol, Direction)> {
    if let Some(rule) = t.forward_rule{
        return Some((rule, Direction::Forward));
    } else if let Some(rule) = t.backward_rule{
        return Some((rule, Direction::Backward));
    } else {
        for child in t.children.iter(){
            if let Some(res) = get_rewrite_name_and_direction(child){
                return Some(res);
            }
        }
    }
    return None;
}

#[allow(unused)]
pub fn make_rule_table(rules: &Vec<Rewrite>) -> HashMap<Symbol, &Rewrite> {
    let mut table: HashMap<Symbol, &Rewrite> = Default::default();
    for r in rules {
        table.insert(r.name, &r);
    }
    table
}

// Remove rewrite labels and put a "?" in the subexpression to be rewritten.
pub fn expected_expr_with_hole(ft : &FlatTerm<Optimization>) -> FlatTerm<Optimization> {
    if ft.forward_rule.is_some() || ft.backward_rule.is_some() { 
        FlatTerm::new(Optimization::Symbol("?".into()), vec![])
    } else { 
        FlatTerm::new(
            ft.node.clone(),
            ft.children
                .iter()
                .map(|child| expected_expr_with_hole(child))
                .collect()
        )
    }
}

// These are functions taken from `explain.rs` removing the assertions.

#[allow(unused)]
fn flat_term_make_bindings_no_failure<'a>(
    term: &'a FlatTerm<Optimization>,
    pattern: &[ENodeOrVar<Optimization>],
    location: usize,
    bindings: &mut HashMap<Var, &'a FlatTerm<Optimization>>,
) -> bool {
    match &pattern[location] {
        ENodeOrVar::Var(var) => {
            if let Some(existing) = bindings.get(var) {
                return existing == &term;
            } else {
                bindings.insert(*var, term);
                return true;
            }
        }
        ENodeOrVar::ENode(node) => {
            if !node.matches(&term.node) {
                return false;
            }
            let mut counter = 0;
            for &child in node.children().iter() {
                if !flat_term_make_bindings_no_failure(&term.children[counter], pattern, usize::from(child), bindings) {
                    return false;
                }
                counter += 1;
            }
            return true;
        }
    }
}

#[allow(unused)]
fn flat_term_from_pattern(
    pattern: &[ENodeOrVar<Optimization>],
    location: usize,
    bindings: &HashMap<Var, &FlatTerm<Optimization>>,
) -> FlatTerm<Optimization> {
    match &pattern[location] {
        ENodeOrVar::Var(var) => (*bindings.get(var).unwrap()).clone(),
        ENodeOrVar::ENode(node) => {
            let children = node.fold(vec![], |mut acc, child| {
                acc.push(flat_term_from_pattern(
                    pattern,
                    usize::from(child),
                    bindings,
                ));
                acc
            });
            FlatTerm::new(node.clone(), children)
        }
    }
}

#[allow(unused)]
fn flat_term_rewrite_no_failure(
    term: &FlatTerm<Optimization>, 
    lhs: &PatternAst<Optimization>, 
    rhs: &PatternAst<Optimization>) -> 
    Option<FlatTerm<Optimization>> {
    let lhs_nodes = lhs.as_ref();
    let rhs_nodes = rhs.as_ref();
    let mut bindings = Default::default();
    if !flat_term_make_bindings_no_failure(term, lhs_nodes, lhs_nodes.len() - 1, &mut bindings) {
        return None;
    }
    return Some(flat_term_from_pattern(rhs_nodes, rhs_nodes.len() - 1, &bindings));
}

#[allow(unused)]
pub fn flat_term_check_rewrite_no_failure<'a>(
    current: &'a FlatTerm<Optimization>,
    next: &'a FlatTerm<Optimization>,
    rewrite: &Rewrite) ->
    bool {
    if let Some(lhs) = rewrite.searcher.get_pattern_ast() {
        if let Some(rhs) = rewrite.applier.get_pattern_ast() {
            if let Some(rewritten) = flat_term_rewrite_no_failure(current, lhs, rhs) {
                return rewritten.eq(next);
            }
        }
    }
    return false;
}
