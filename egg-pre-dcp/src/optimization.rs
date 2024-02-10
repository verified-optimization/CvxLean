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
        "inv" = Inv(Id),
        "abs" = Abs(Id),
        "sqrt" = Sqrt(Id),
        "log" = Log(Id),
        "exp" = Exp(Id),
        "xexp" = XExp(Id),
        "entr" = Entr(Id),
        "min" = Min([Id; 2]),
        "max" = Max([Id; 2]),
        "add" = Add([Id; 2]),
        "sub" = Sub([Id; 2]),
        "mul" = Mul([Id; 2]),
        "div" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "qol" = QOL([Id; 2]),
        "geo" = Geo([Id; 2]),
        "lse" = LSE([Id; 2]),
        "norm2" = Norm2([Id; 2]),
        "var" = Var(Id),
        "param" = Param(Id),
        "pi" = Pi([Id; 0]),
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
    pub is_constant: bool,
}

impl Analysis<Optimization> for Meta {    
    type Data = Data;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let d_before_o = to.domain.clone();
        match (to.domain.clone(), from.domain.clone()) {
            (None, Some(_)) => { to.domain = from.domain.clone(); }
            (Some(d_to), Some(d_from)) => {
                if !d_to.eq(&d_from) {
                    let inter = d_to.intersection(&d_from);
                    if Domain::is_empty(&inter) {
                        // Should never get here for feasible problems.
                        to.domain = None
                    } else {
                        to.domain = Some(inter); 
                    }
                }
            }
            _ => ()
        }
        let to_domain_diff = 
            match (d_before_o, to.domain.clone()) {
                (Some(d_before), Some(d_to)) => !d_before.eq(&d_to),
                (None, None) => false,
                _ => true
            };
        let from_domain_diff = 
            match (to.domain.clone(), from.domain.clone()) {
                (Some(d_to), Some(d_from)) => !d_to.eq(&d_from),
                (None, None) => false,
                _ => true
            };
        
        let is_constant_before = to.is_constant.clone();
        to.is_constant = to.is_constant || from.is_constant;
        let to_is_constant_diff = is_constant_before != to.is_constant;
        let from_is_constant_diff = to.is_constant != from.is_constant;

        DidMerge(
            to_domain_diff || to_is_constant_diff, 
            from_domain_diff || from_is_constant_diff)
    }

    fn make(egraph: &EGraph, enode: &Optimization) -> Self::Data {
        let get_domain = 
            |i: &Id| egraph[*i].data.domain.clone();
        let get_is_constant = 
            |i: &Id| egraph[*i].data.is_constant.clone();

        let domains_map = 
            egraph.analysis.domains.clone();

        let mut domain = None;
        let mut is_constant = false;

        match enode {
            Optimization::Neg(a) => {
                domain = domain::option_neg(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::Inv(a) => {
                domain = domain::option_inv(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::Abs(a) => {
                domain = domain::option_abs(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::Sqrt(a) => {
                domain = domain::option_sqrt(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::Log(a) => {
                domain = domain::option_log(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::Exp(a) => {
                domain = domain::option_exp(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::XExp(a) => {
                domain = domain::option_xexp(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::Entr(a) => {
                domain = domain::option_entr(get_domain(a));
                is_constant = get_is_constant(a);
            }
            Optimization::Min([a, b]) => {
                domain = domain::option_min(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Max([a, b]) => {
                domain = domain::option_max(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Add([a, b]) => {
                domain = domain::option_add(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Sub([a, b]) => {
                domain = domain::option_sub(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Mul([a, b]) => {
                domain = domain::option_mul(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Div([a, b]) => {
                domain = domain::option_div(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Pow([a, b]) => {
                domain = domain::option_pow(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::QOL([a, b]) => {
                domain = domain::option_quad_over_lin(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Geo([a, b]) => {
                domain = domain::option_geo_mean(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::LSE([a, b]) => {
                domain = domain::option_log_sum_exp(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Norm2([a, b]) => {
                domain = domain::option_norm2(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Var(a) => {
                // Assume that after var there is always a symbol.
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        let s_s = format!("{}", s); 
                        match domains_map.get(&s_s) {
                            Some(d) => { domain = Some(d.clone()); }
                            _ => { domain = Some(domain::free_dom()); }
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
                            _ => { domain = Some(domain::free_dom()); }
                        }
                    }
                    _ => {}
                }
                // NOTE(RFM): parameters are treated as constants.
                is_constant = true;
            } 
            Optimization::Pi(_) => {
                domain = Some(Domain::make_singleton(std::f64::consts::PI));
                is_constant = true;
            }
            Optimization::Symbol(_) => {}
            Optimization::Constant(f) => {
                domain = Some(Domain::make_singleton((*f).into_inner()));
                is_constant = true;
            }
            _ => {}
        }

        Data { domain, is_constant }
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

#[allow(unused)]
pub fn is_lt_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data.domain {
            return domain::is_neg(d);
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

pub fn is_le_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data.domain {
            return domain::is_nonpos(d);
        }
        return false;
    }
}

pub fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data.domain {
            return domain::does_not_contain_zero(d);
        }
        return false;
    }
}

pub fn is_nat(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d) = &egraph[subst[var]].data.domain {
            if let Some(c) = Domain::get_constant(d) {
                return ((c as u32) as f64) == c;
            }
        }
        return false;
    }
}

pub fn is_le(var1: &str, var2: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var1 = var1.parse().unwrap();
    let var2 = var2.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(d1) = &egraph[subst[var1]].data.domain {
            if let Some(d2) = &egraph[subst[var2]].data.domain {
                return Domain::subseteq(d1, d2);
            }
        }
        return false;
    }
}

pub fn is_ge(var1: &str, var2: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    is_le(var2, var1)
}
