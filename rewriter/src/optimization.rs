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
    pub has_log: bool,
}

impl Analysis<Optimization> for Meta {    
    type Data = Data;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        let has_log_before = to.has_log;
        to.has_log = to.has_log || from.has_log;
        let to_has_log_diff = has_log_before != to.has_log;
        let from_has_log_diff = to.has_log != from.has_log;

        let before_domain = to.domain.clone();
        match (to.domain, from.domain) {
            (None, Some(_)) => { to.domain = from.domain; }
            (Some(d_to), Some(d_from)) => {
                if d_to != d_from { to.domain = None; }
            }
            _ => ()
        }
        let to_domain_diff = before_domain != to.domain;
        let from_domain_diff = to.domain != from.domain;

        DidMerge(
            to_has_log_diff || to_domain_diff,
            from_has_log_diff || from_domain_diff,
        )
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
        let mut has_log = false;

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
                domain = domain::option_flip(get_domain(a));
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

                let d_o_a = get_domain(a);
                match d_o_a {
                    Some(d_a) => { 
                        if domain::is_nonneg(d_a) {
                            domain = d_o_a;
                        } 
                        // NOTE(RFM): If argument is negative, sqrt in Lean 
                        // returns zero, but we treat as if it didn't have a 
                        // domain.
                    }
                    _ => ()
                }
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
                domain = domain::option_add(
                    get_domain(a), 
                    domain::option_flip(get_domain(b)));
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
                domain = domain::option_mul(
                    get_domain(a), get_domain(b))
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

                let d_o_b = get_domain(b);
                match d_o_b {
                    Some(d_b) => {
                        if domain::is_pos(d_b) || domain::is_neg(d_b) {
                            domain = domain::option_mul(
                                get_domain(a), d_o_b);
                        }
                    },
                    _ => ()
                }
            }
            Optimization::Pow([a, b]) => {
                let d_o_a = get_domain(a);
                let d_o_b = get_domain(b);
                match (d_o_a, d_o_b) {
                    (Some(d_a), Some(d_b)) => { 
                        if !domain::is_zero(d_a) && domain::is_zero(d_b) {
                            // NOTE(RFM): This is technically 1.
                            domain = Some(Domain::PosConst);
                        } else if domain::is_pos(d_a) {
                            domain = d_o_a;
                        }
                        // NOTE(RFM): There could be more cases here.
                    }
                    _ => ()
                }
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
                has_log = true;
                
                let d_o_a = get_domain(a);
                match d_o_a {
                    Some(d_a) => {
                        if domain::is_pos(d_a) {
                            // NOTE(RFM): We do not know if the argument is less 
                            // than 1 or not, so that's all we can say.
                            domain = Some(Domain::Free);
                        }
                    }
                    _ => ()
                }
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

                domain = Some(Domain::Pos);
            }
            Optimization::Var(a) => {
                // Assume that after var there is always a symbol.
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        let s_s = format!("{}", s); 
                        match domains_map.get(&s_s) {
                            Some(d) => { domain = Some(*d); }
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
                            Some(d) => { domain = Some(*d); }
                            _ => ()
                        }
                    }
                    _ => {}
                }
            } 
            Optimization::Symbol(_) => {}
            Optimization::Constant(f) => {
                constant = Some((*f, format!("{}", f).parse().unwrap()));
                if (*f).is_finite() {
                    if (*f).into_inner() > 0.0 {
                        domain = Some(Domain::PosConst);
                    } else if (*f).into_inner() < 0.0 {
                        domain = Some(Domain::NegConst);
                    } else {
                        domain = Some(Domain::Zero);
                    }
                }
            }
            _ => {}
        }

        Data { constant, domain, has_log }
    }
}

pub fn is_gt_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            (*n).into_inner() > 0.0
        } else {
            if let Some(d) = &egraph[subst[var]].data.domain {
                return domain::is_pos(*d);
            }
            return false;
        }
    }
}

pub fn is_ge_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            (*n).into_inner() >= 0.0
        } else {
            if let Some(d) = &egraph[subst[var]].data.domain {
                return domain::is_nonneg(*d);
            }
            return false;
        }
    }
}

pub fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            (*n).into_inner() != 0.0
        } else {
            if let Some(d) = &egraph[subst[var]].data.domain {
                return domain::is_nonzero(*d);
            }
            return false;
        }
    }
}

pub fn not_has_log(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        !egraph[subst[var]].data.has_log
    }
}
