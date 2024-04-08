use egg::{*};
use std::collections::HashMap;
use ordered_float::NotNan;

use crate::domain;
use domain::Domain as Domain;

#[cfg(stop_on_success)]
use crate::curvature;
#[cfg(stop_on_success)]
use curvature::Curvature as Curvature;

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

#[cfg(not(stop_on_success))]
#[derive(Debug, Clone)]
pub struct Data {
    pub domain: Option<Domain>,
    pub is_constant: bool,
}

#[cfg(not(stop_on_success))]
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

#[cfg(stop_on_success)]
#[derive(Debug, Clone)]
pub struct DataWithCost {
    pub domain: Option<Domain>,
    pub is_constant: bool,
    pub curvature: Curvature, 
    pub best: RecExpr<Optimization>,
    pub num_vars: u32,
    pub term_size: u32,
}

#[cfg(stop_on_success)]
impl Analysis<Optimization> for Meta {    
    type Data = DataWithCost;

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
        
        let curvature_before = to.curvature.clone();
        let best_before = to.best.clone();
        let num_vars_before = to.num_vars.clone();
        let term_size_before = to.term_size.clone();
        if from.curvature < to.curvature {
            to.curvature = from.curvature.clone();
            to.best = from.best.clone();
            to.num_vars = from.num_vars.clone();
            to.term_size = from.term_size.clone();
        } else if to.curvature == from.curvature {
            // Select smallest "best".
            if (from.num_vars, from.term_size) < (to.num_vars, to.term_size) {
                to.best = from.best.clone();
                to.num_vars = from.num_vars.clone();
                to.term_size = from.term_size.clone();
            }
        }
        let to_curvature_diff = curvature_before != to.curvature;
        let to_best_diff = best_before != to.best;
        let to_num_vars_diff = num_vars_before != to.num_vars;
        let to_term_size_diff = term_size_before != to.term_size;
        let from_curvature_diff = to.curvature != from.curvature;
        let from_best_diff = to.best != from.best;
        let from_num_vars_diff = to.num_vars != from.num_vars;
        let from_term_size_diff = to.term_size != from.term_size;

        DidMerge(
            to_domain_diff || to_is_constant_diff || to_curvature_diff || to_best_diff || 
            to_num_vars_diff || to_term_size_diff, 
            from_domain_diff || from_is_constant_diff || from_curvature_diff || from_best_diff || 
            from_num_vars_diff || from_term_size_diff)
    }

    fn make(egraph: &EGraph, enode: &Optimization) -> Self::Data {
        let get_domain = 
            |i: &Id| egraph[*i].data.domain.clone();
        let get_is_constant = 
            |i: &Id| egraph[*i].data.is_constant.clone();
        let get_curvature = 
            |i: &Id| egraph[*i].data.curvature.clone();
        let get_best = 
            |i: &Id| egraph[*i].data.best.clone();
        let get_num_vars = 
            |i: &Id| egraph[*i].data.num_vars.clone();
        let get_term_size = 
            |i: &Id| egraph[*i].data.term_size.clone();

        let domains_map = 
            egraph.analysis.domains.clone();

        let mut domain = None;
        let mut is_constant = false;
        let mut curvature = Curvature::Unknown;
        let mut best = RecExpr::default();
        let mut num_vars = 0;
        let mut term_size = 0;

        match enode {
            Optimization::Prob([a, b]) => {
                curvature = 
                    if get_curvature(a) >= get_curvature(b) {
                        get_curvature(a)
                    } else if get_curvature(b) >= get_curvature(a) {
                        get_curvature(b)
                    } else {
                        // Should not get here.
                        Curvature::Unknown
                    };
                best = format!("(prob {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::ObjFun(a) => {
                // It cannot be concave, because of mapping functions.
                curvature = 
                    if get_curvature(a) <= Curvature::Convex {
                        get_curvature(a)
                    } else {
                        Curvature::Unknown
                    };
                best = format!("(objFun {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Constr([h, c]) => {
                // It cannot be concave, because the notion of concavity at the Prop (or set) level
                // is not well-defined.
                curvature = 
                    if get_curvature(c) <= Curvature::Convex {
                        get_curvature(c)
                    } else {
                        Curvature::Unknown
                    };
                best = format!("(constr {} {})", get_best(h), get_best(c)).parse().unwrap();
                num_vars = get_num_vars(c);
                term_size = 1 + get_term_size(c);
            }
            Optimization::Constrs(a) => {
                curvature = Curvature::Constant;
                term_size = 0;
                num_vars = 0;
                for c in a.iter() {
                    if curvature < get_curvature(c) {
                        curvature = get_curvature(c);
                    }
                    num_vars += get_num_vars(c);
                    term_size += get_term_size(c);
                }
                let constrs_s_l : Vec<String> = 
                    a.iter().map(|c| format!("{}", get_best(c))).collect();
                best = format!("(constrs {})", constrs_s_l.join(" ")).parse().unwrap();
            }
            Optimization::Eq([a, b]) => {
                if get_curvature(a) <= Curvature::Affine && get_curvature(b) <= Curvature::Affine {
                    curvature = Curvature::Affine
                }
                best = format!("(eq {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Le([a, b]) => {
                curvature = curvature::of_le(get_curvature(a), get_curvature(b));
                best = format!("(le {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Neg(a) => {
                domain = domain::option_neg(get_domain(a));
                is_constant = get_is_constant(a);
                curvature = curvature::of_neg(get_curvature(a));
                best = format!("(neg {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Inv(a) => {
                domain = domain::option_inv(get_domain(a));
                is_constant = get_is_constant(a);
                let da_pos = domain::option_is_pos(get_domain(a).as_ref());
                if da_pos {
                    curvature = curvature::of_convex_nonincreasing_fn(get_curvature(a));
                }
                best = format!("(inv {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Abs(a) => {
                domain = domain::option_abs(get_domain(a));
                is_constant = get_is_constant(a);
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                let da_nonpos = domain::option_is_nonpos(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_convex_nondecreasing_fn(get_curvature(a));
                } else if da_nonpos {
                    curvature = curvature::of_convex_nonincreasing_fn(get_curvature(a));
                } else {
                    curvature = curvature::of_convex_none_fn(get_curvature(a));
                }
                best = format!("(abs {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Sqrt(a) => {
                domain = domain::option_sqrt(get_domain(a));
                is_constant = get_is_constant(a);
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_concave_nondecreasing_fn(get_curvature(a));
                }
                best = format!("(sqrt {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Log(a) => {
                domain = domain::option_log(get_domain(a));
                is_constant = get_is_constant(a);
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_concave_nondecreasing_fn(get_curvature(a));
                }
                best = format!("(log {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Exp(a) => {
                domain = domain::option_exp(get_domain(a));
                is_constant = get_is_constant(a);
                curvature = curvature::of_convex_nondecreasing_fn(get_curvature(a));
                best = format!("(exp {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::XExp(a) => {
                domain = domain::option_xexp(get_domain(a));
                is_constant = get_is_constant(a);
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_convex_nondecreasing_fn(get_curvature(a));
                }
                best = format!("(xexp {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Entr(a) => {
                domain = domain::option_entr(get_domain(a));
                is_constant = get_is_constant(a);
                let da_pos = domain::option_is_pos(get_domain(a).as_ref());
                if da_pos {
                    curvature = curvature::of_concave_none_fn(get_curvature(a));
                }
                best = format!("(entr {})", get_best(a)).parse().unwrap();
                num_vars = get_num_vars(a);
                term_size = 1 + get_term_size(a);
            }
            Optimization::Min([a, b]) => {
                domain = domain::option_min(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let curvature_a = curvature::of_concave_nondecreasing_fn(get_curvature(a));
                let curvature_b = curvature::of_concave_nondecreasing_fn(get_curvature(b));
                curvature = curvature::join(curvature_a, curvature_b);
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Max([a, b]) => {
                domain = domain::option_max(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let curvature_a = curvature::of_convex_nondecreasing_fn(get_curvature(a));
                let curvature_b = curvature::of_convex_nondecreasing_fn(get_curvature(b));
                curvature = curvature::join(curvature_a, curvature_b);
                best = format!("(max {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Add([a, b]) => {
                domain = domain::option_add(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                curvature = curvature::of_add(get_curvature(a), get_curvature(b));
                best = format!("(add {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Sub([a, b]) => {
                domain = domain::option_sub(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                curvature = curvature::of_sub(get_curvature(a), get_curvature(b));
                best = format!("(sub {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Mul([a, b]) => {
                domain = domain::option_mul(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let da_o = get_domain(a);
                let db_o = get_domain(b);
                match (get_is_constant(a), get_is_constant(b)) {
                    (true, true) => { 
                        curvature = Curvature::Constant
                    }
                    (true, false) => {
                        if let Some(da) = da_o {
                            curvature = curvature::of_mul_by_const(get_curvature(b), da)
                        }
                    }
                    (false, true) => {
                        if let Some(db) = db_o {
                            curvature = curvature::of_mul_by_const(get_curvature(a), db)
                        }
                    }
                    _ => { }
                }
                best = format!("(mul {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Div([a, b]) => {
                domain = domain::option_div(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let db_o = get_domain(b);
                match (get_is_constant(a), get_is_constant(b)) {
                    (true, true) => {
                        if let Some(db) = db_o {
                            if domain::does_not_contain_zero(&db) {
                                curvature = Curvature::Constant
                            }
                        }
                    }
                    (false, true) => {
                        if let Some(db) = db_o {
                            if domain::does_not_contain_zero(&db) {
                                curvature = curvature::of_mul_by_const(get_curvature(a), db)
                            }
                        }
                    }
                    _ => { }
                };
                best = format!("(div {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Pow([a, b]) => {
                domain = domain::option_pow(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                if get_is_constant(b) {
                    if let Some(db) = get_domain(b) {
                        // Domain guards already in `of_pow_by_const`.
                        curvature = curvature::of_pow_by_const(get_curvature(a), db, get_domain(a))
                    }
                } 
                best = format!("(pow {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::QOL([a, b]) => {
                domain = domain::option_quad_over_lin(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let curvature_num = curvature::of_convex_none_fn(get_curvature(a));
                let db_pos = domain::option_is_pos(get_domain(b).as_ref());
                if db_pos {
                    let curvature_den = curvature::of_convex_nonincreasing_fn(get_curvature(b));
                    curvature = curvature::join(curvature_num, curvature_den);
                }
                best = format!("(qol {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Geo([a, b]) => {
                domain = domain::option_geo_mean(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                let db_nonneg = domain::option_is_nonneg(get_domain(b).as_ref());
                if da_nonneg && db_nonneg {
                    let curvature_a = curvature::of_concave_nondecreasing_fn(get_curvature(a));
                    let curvature_b = curvature::of_concave_nondecreasing_fn(get_curvature(b));
                    curvature = curvature::join(curvature_a, curvature_b);
                }
                best = format!("(geo {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::LSE([a, b]) => {
                domain = domain::option_log_sum_exp(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let curvature_a = curvature::of_convex_nondecreasing_fn(get_curvature(a));
                let curvature_b = curvature::of_convex_nondecreasing_fn(get_curvature(b));
                curvature = curvature::join(curvature_a, curvature_b);
                best = format!("(lse {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
            }
            Optimization::Norm2([a, b]) => {
                domain = domain::option_norm2(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                let curvature_a = curvature::of_convex_none_fn(get_curvature(a));
                let curvature_b = curvature::of_convex_none_fn(get_curvature(b));
                curvature = curvature::join(curvature_a, curvature_b);
                best = format!("(norm2 {} {})", get_best(a), get_best(b)).parse().unwrap();
                num_vars = get_num_vars(a) + get_num_vars(b);
                term_size = 1 + get_term_size(a) + get_term_size(b);
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
                        curvature = Curvature::Affine;
                        best = format!("(var {})", s).parse().unwrap();
                        num_vars = 1;
                        term_size = 1;
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
                        curvature = Curvature::Constant;
                        best = format!("(param {})", s).parse().unwrap();
                        num_vars = 0;
                        term_size = 1;
                    }
                    _ => {}
                }
                // NOTE(RFM): parameters are treated as constants.
                is_constant = true;
                
            } 
            Optimization::Pi(_) => {
                domain = Some(Domain::make_singleton(std::f64::consts::PI));
                is_constant = true;
                curvature = Curvature::Constant;
                best = format!("pi").parse().unwrap();
                num_vars = 0;
                term_size = 1;
            }
            Optimization::Symbol(s) => {
                best = format!("{}", s).parse().unwrap();
                num_vars = 0;
                term_size = 0;
            }
            Optimization::Constant(f) => {
                domain = Some(Domain::make_singleton((*f).into_inner()));
                is_constant = true;
                curvature = Curvature::Constant;
                best = format!("{}", f).parse().unwrap();
                num_vars = 0;
                term_size = 1;
            }
        }

        if is_constant {
            term_size = 1;
        }

        DataWithCost { domain, is_constant, curvature, best, num_vars, term_size }
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
