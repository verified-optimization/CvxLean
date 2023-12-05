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
        "log" = Log(Id),
        "exp" = Exp(Id),
        "xexp" = XExp(Id),
        "entr" = Entr(Id),
        "add" = Add([Id; 2]),
        "sub" = Sub([Id; 2]),
        "mul" = Mul([Id; 2]),
        "div" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "qol" = QOL([Id; 2]),
        "geo" = Geo([Id; 2]),
        "norm2" = Norm2([Id; 2]),
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
    pub is_constant: bool,
}

fn make_constant_repr_unary<F>(symbol: &str, f: F, val_o: Option<Constant>) -> 
    Option<(Constant, PatternAst<Optimization>)> 
    where
        F: Fn(Constant) -> Constant {
    match val_o {
        Some(val) => { 
            let res = f(val);
            let res_f = res.into_inner();
            if ((2.0 * res_f) as u32) as f64 == (2.0 * res_f) {
                Some((res, format!("({} {})", symbol, val).parse().unwrap())) 
            } else {
                None
            }
        }
        _ => None
    }
}

fn make_constant_repr_binary<F>(symbol: &str, f: F, val1_o: Option<Constant>, val2_o: Option<Constant>) -> 
    Option<(Constant, PatternAst<Optimization>)> 
    where
        F: Fn(Constant, Constant) -> Constant {
    match (val1_o, val2_o) {
        (Some(val1), Some(val2)) => { 
            let res = f(val1, val2);
            let res_f = res.into_inner();
            if ((2.0 * res_f) as u32) as f64 == (2.0 * res_f) {
                Some((res, format!("({} {} {})", symbol, val1, val2).parse().unwrap())) 
            } else {
                None
            }
        }
        _ => None
    }
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
                        // Should never get here.
                        println!("Empty domain.");
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
        let repr = 
            |i: &Id| egraph[*i].data.constant_repr.clone().map(|d| d.0);

        let domains_map = 
            egraph.analysis.domains.clone();

        let mut domain = None;
        let mut is_constant = false;
        let mut constant_repr = None;

        match enode {
            Optimization::Neg(a) => {
                domain = domain::option_neg(get_domain(a));
                is_constant = get_is_constant(a);
                if is_constant {
                    constant_repr = 
                        make_constant_repr_unary("neg", |x| -x, repr(a))
                }
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
            Optimization::Add([a, b]) => {
                domain = domain::option_add(
                    get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                if is_constant {
                    constant_repr = 
                        make_constant_repr_binary("add", |x, y| x + y, repr(a), repr(b))
                }
            }
            Optimization::Sub([a, b]) => {
                domain = domain::option_sub(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                if is_constant {
                    constant_repr = 
                        make_constant_repr_binary("sub", |x, y| x - y, repr(a), repr(b))
                }
            }
            Optimization::Mul([a, b]) => {
                domain = domain::option_mul(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                if is_constant {
                    constant_repr = 
                        make_constant_repr_binary("mul", |x, y| x * y, repr(a), repr(b))
                }
            }
            Optimization::Div([a, b]) => {
                domain = domain::option_div(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                if is_constant {
                    constant_repr = 
                        make_constant_repr_binary("div", |x, y| x / y, repr(a), repr(b))
                }
            }
            Optimization::Pow([a, b]) => {
                domain = domain::option_pow(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
                if is_constant {
                    constant_repr = 
                        make_constant_repr_binary("pow", |x, y| Pow::pow(x, y), repr(a), repr(b))
                }
            }
            Optimization::QOL([a, b]) => {
                domain = domain::option_quad_over_lin(get_domain(a), get_domain(b));
                is_constant = get_is_constant(a) && get_is_constant(b);
            }
            Optimization::Geo([a, b]) => {
                domain = domain::option_geo_mean(get_domain(a), get_domain(b));
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
            Optimization::Symbol(_) => {}
            Optimization::Constant(f) => {
                domain = Some(Domain::make_singleton((*f).into_inner()));
                is_constant = true;
                constant_repr = Some((*f, format!("{}", f).parse().unwrap())); 
            }
            _ => {}
        }

        Data { domain, is_constant, constant_repr }
    }

    fn modify(egraph: &mut egg::EGraph<Optimization, Self>, id: Id) {
        let data = egraph[id].data.clone();
        if !data.is_constant {
            return;
        }
        let c_from_domain;
        match data.domain {
            Some(d) => {
                match d.get_constant() {
                    Some(c) => { c_from_domain = c; }
                    _ => { return; }
                }
            }
            _ => { return; }
        }
        match data.constant_repr {
            Some((c, pat)) => {
                let c_f = c.into_inner();
                if c_f != c_from_domain {
                    // Should never get here.
                    print!("Constants do not match {c_f} {c_from_domain}.");
                    return;
                }
                // egraph.union_instantiations(
                //     &pat,
                //     &format!("{}", c_from_domain).parse().unwrap(),
                //     &Default::default(),
                //     "constant_fold".to_string(),
                // );
                let nn_c = NotNan::new(c_f).unwrap();
                let node = Optimization::Constant(nn_c);
                let added = egraph.add(node);
                egraph.union_trusted(id, added, "constant_fold");

                egraph[id].assert_unique_leaves();
}
            _ => {}
        }
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
            return domain::does_not_contain_zero(d);
        }
        return false;
    }
}
