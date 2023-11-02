use egg::{*};
use std::collections::HashMap;
use ordered_float::NotNan;

use crate::domain;
use domain::Domain as Domain;

pub type Constant = NotNan<f64>;

define_language! {
    pub enum Optimization {
        "prob" = Prob([Id; 2]),
        "objFun" = ObjFun(Id),
        "constr" = Constr([Id; 2]),
        "constrs" = Constrs(Box<[Id]>),
        "eq" = Eq([Id; 2]),
        "le" = Le([Id; 2]),
        "neg" = Neg(Id),
        "sqrt" = Sqrt(Id),
        "add" = Add([Id; 2]),
        "sub" = Sub([Id; 2]),
        "mul" = Mul([Id; 2]),
        "div" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "log" = Log(Id),
        "exp" = Exp(Id),
        "var" = Var(Id),
        "param" = Param(Id),
        Constant(Constant),
        Symbol(Symbol),
    }
}

pub type EGraph = egg::EGraph<Optimization, Meta>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    pub domains : HashMap<String, Domain>,
}

#[derive(Debug, Clone)]
pub struct Data {
    pub domain: Option<Domain>,
    pub constant: Option<(Constant, PatternAst<Optimization>)>,
}

impl Analysis<Optimization> for Meta {    
    type Data = Data;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let before_domain = to.domain.clone();
        match (to.domain.clone(), from.domain.clone()) {
            (None, Some(_)) => { to.domain = from.domain.clone(); }
            (Some(d_to), Some(d_from)) => {
                if !domain::eq(&d_to, &d_from) {
                    to.domain = Some(domain::intersection(&d_to, &d_from)); 
                }
            }
            _ => ()
        }
        let to_domain_diff = 
            match (before_domain, to.domain.clone()) {
                (Some(d_before), Some(d_to)) => !domain::eq(&d_before, &d_to),
                (None, None) => false,
                _ => true
            };
        let from_domain_diff = 
            match (to.domain.clone(), from.domain.clone()) {
                (Some(d_to), Some(d_from)) => !domain::eq(&d_to, &d_from),
                (None, None) => false,
                _ => true
            };

        DidMerge(to_domain_diff, from_domain_diff)
    }

    fn make(egraph: &EGraph, enode: &Optimization) -> Self::Data {
        let get_constant = 
            |i: &Id| egraph[*i].data.constant.clone();
        let get_domain = 
            |i: &Id| egraph[*i].data.domain.clone();
        let domains_map = 
            egraph.analysis.domains.clone();

        let mut constant = None;
        let mut domain = None;

        match enode {
            Optimization::Neg(a) => {
                match get_constant(a) {
                    Some((c, _)) => { 
                        constant = Some((
                            -c, 
                            format!("(neg {})", c).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_neg(get_domain(a));
            }
            Optimization::Sqrt(a) => {
                match get_constant(a) {
                    Some((c, _)) => { 
                        constant = Some((
                            NotNan::new(c.sqrt()).unwrap(), 
                            format!("(sqrt {})", c).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_sqrt(get_domain(a));
            }
            Optimization::Add([a, b]) => {
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((
                            c1 + c2, 
                            format!("(add {} {})", c1, c2).parse().unwrap())); 
                    }
                    _ => {}
                }

                domain = domain::option_add(
                    get_domain(a), get_domain(b));
            }
            Optimization::Sub([a, b]) => {
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((
                            c1 - c2, 
                            format!("(sub {} {})", c1, c2).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_sub(get_domain(a), get_domain(b));
            }
            Optimization::Mul([a, b]) => {
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((
                            c1 * c2, 
                            format!("(mul {} {})", c1, c2).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_mul(get_domain(a), get_domain(b));
            }
            Optimization::Div([a, b]) => {
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((
                            c1 / c2, 
                            format!("(div {} {})", c1, c2).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_div(get_domain(a), get_domain(b));
            }
            Optimization::Pow([a, b]) => {
                match (get_constant(a), get_constant(b)) {
                    (Some((c1, _)), Some((c2, _))) => { 
                        constant = Some((
                            NotNan::new(c1.powf(c2.into())).unwrap(), 
                            format!("(pow {} {})", c1, c2).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_pow(get_domain(a), get_domain(b))
            }
            Optimization::Log(a) => {
                match get_constant(a) {
                    Some((c, _)) => { 
                        constant = Some((
                            NotNan::new(c.ln()).unwrap(), 
                            format!("(log {})", c).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_log(get_domain(a));
            }
            Optimization::Exp(a) => {
                match get_constant(a) {
                    Some((c, _)) => { 
                        constant = Some((
                            NotNan::new(c.exp()).unwrap(), 
                            format!("(exp {})", c).parse().unwrap())); 
                    }
                    _ => {}
                }
                domain = domain::option_exp(get_domain(a));
            }
            Optimization::Var(a) => {
                // Assume that after var there is always a symbol.
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        let s_s = format!("{}", s); 
                        match domains_map.get(&s_s) {
                            Some(d) => { domain = Some(d.clone()); }
                            _ => ()
                        }
                    }
                    _ => {}
                }
            }
            Optimization::Param(a) => {
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        let s_s = format!("{}", s); 
                        match domains_map.get(&s_s) {
                            Some(d) => { domain = Some(d.clone()); }
                            _ => ()
                        }
                    }
                    _ => {}
                }
            } 
            Optimization::Symbol(_) => {}
            Optimization::Constant(f) => {
                constant = Some((*f, format!("{}", f).parse().unwrap()));
                domain = Some(domain::singleton((*f).into_inner()));
            }
            _ => {}
        }

        // println!("{}: {:?}", enode, domain);
        Data { constant, domain }
    }
}

pub fn is_gt_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data.domain {
            return domain::is_pos(d);
        }
        return false;
    }
}

pub fn is_ge_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data.domain {
            return domain::is_nonneg(d);
        }
        return false;
    }
}

pub fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data.domain {
            return domain::is_nonzero(d);
        }
        return false;
    }
}
