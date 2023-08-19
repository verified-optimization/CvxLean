use egg::{rewrite as rw, *};
use std::collections::{HashMap, HashSet};
use ordered_float::NotNan;
use std::{fs, io};
use serde::{Deserialize, Serialize};

mod domain;
use domain::Domain as Domain;

mod curvature;
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

type EGraph = egg::EGraph<Optimization, Meta>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    domains : HashMap<Symbol, Domain>,
}

#[derive(Debug, Clone)]
pub struct Data {
    free_vars: HashSet<(Id, Symbol)>,
    domain: Option<Domain>,
    constant: Option<(Constant, PatternAst<Optimization>)>,
    has_log: bool,
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

        let before_free_vars = to.free_vars.len();
        to.free_vars.retain(|i| from.free_vars.contains(i));
        let to_free_vars_diff = before_free_vars != to.free_vars.len();
        let from_free_vars_diff = to.free_vars.len() != from.free_vars.len();

        DidMerge(
            to_has_log_diff || to_domain_diff || to_free_vars_diff,
            from_has_log_diff || from_domain_diff || from_free_vars_diff,
        )
    }

    fn make(egraph: &EGraph, enode: &Optimization) -> Self::Data {
        let get_vars = 
            |i: &Id| egraph[*i].data.free_vars.iter().cloned();
        let get_constant = 
            |i: &Id| egraph[*i].data.constant.clone();
        let get_domain = 
            |i: &Id| egraph[*i].data.domain.clone();
        let domains_map = 
            egraph.analysis.domains.clone();

        let mut free_vars = HashSet::default();
        let mut constant = None;
        let mut domain = None;
        let mut has_log = false;

        match enode {
            Optimization::Prob([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::ObjFun(a) => {
                free_vars.extend(get_vars(a));
            }
            Optimization::Constr([h, c]) => {
                free_vars.extend(get_vars(c));
            }
            Optimization::Constrs(a) => {
                for c in a.iter() {
                    free_vars.extend(get_vars(c));
                }
            }
            Optimization::Eq([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Le([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::Neg(a) => {
                free_vars.extend(get_vars(a));
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
                free_vars.extend(get_vars(a));
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
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
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
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
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
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
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
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
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
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));

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
                free_vars.extend(get_vars(a));
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
                free_vars.extend(get_vars(a));
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
                        free_vars.insert((*a, s)); 
                        match domains_map.get(&s) {
                            Some(d) => { domain = Some(*d); }
                            _ => ()
                        }
                    }
                    _ => {}
                }
            }
            Optimization::Param(_) => {
                // TODO(RFM): Add domain to parameters.
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
        }

        Data { free_vars, constant, domain, has_log }
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            *(n) != 0.0
        } else {
            true
        }
    }
}

fn is_not_one(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            *(n) != 1.0
        } else {
            true
        }
    }
}

fn is_gt_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((n, _)) = &egraph[subst[var]].data.constant {
            (*n).into_inner() > 0.0
        } else {
            true
        }
    }
}

fn not_has_log(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        !egraph[subst[var]].data.has_log
    }
}

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("eq-add"; "(eq ?a (add ?b ?c))" => "(eq (sub ?a ?c) ?b)"),

    rw!("eq-sub"; "(eq ?a (sub ?b ?c))" => "(eq (add ?a ?c) ?b)"),

    rw!("eq-mul"; "(eq ?a (mul ?b ?c))" => "(eq (div ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("eq-div"; "(eq ?a (div ?b ?c))" => "(eq (mul ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("eq-sub-zero"; "(eq ?a ?b)" => "(eq (sub ?a ?b) 0)"
        if is_not_zero("?b")),

    rw!("eq-div-one"; "(eq ?a ?b)" => "(eq (div ?a ?b) 1)" 
        if is_not_zero("?b") if is_not_one("?b")),

    rw!("le-sub"; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)"),

    rw!("le-add"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)"),

    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_not_zero("?c")),

    // NOTE(RFM): The b != 1 condition is to avoid infinite chains in 
    // combination with le-div-one.
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_not_zero("?c") if is_not_one("?b")),

    rw!("le-div"; "(le ?a (div ?b ?c))" => "(le (mul ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("le-sub-zero"; "(le ?a ?b)" => "(le (sub ?a ?b) 0)" 
        if is_not_zero("?b")),

    rw!("le-div-one"; "(le ?a ?b)" => "(le (div ?a ?b) 1)" 
        if is_not_zero("?b") if is_not_one("?b")),

    rw!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"), 

    rw!("add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
    
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),

    rw!("add-sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),

    rw!("add-mul"; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))"),

    rw!("mul-sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),

    // NOTE(RFM): Testing this.
    rw!("sub-self"; "(sub ?a ?a)" => "0"),

    rw!("sub-mul-left"; "(sub (mul ?a ?b) (mul ?a ?c))" => 
        "(mul ?a (sub ?b ?c))"),

    rw!("sub-mul-right"; "(sub (mul ?a ?b) (mul ?c ?b))" => 
        "(mul (sub ?a ?c) ?b)"),

    rw!("sub-mul-same-right"; "(sub ?a (mul ?b ?a))" => "(mul ?a (sub 1 ?b))"),

    rw!("sub-mul-same-left"; "(sub (mul ?a ?b) ?a)" => "(mul ?a (sub ?b 1))"),

    rw!("mul-div"; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)" 
        if is_not_zero("?c")),

    rw!("div-mul"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),
    
    rw!("div-add"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    rw!("add-div"; "(add (div ?a ?b) (div ?c ?b))" => "(div (add ?a ?c) ?b)"),

    rw!("div-sub"; "(div (sub ?a ?b) ?c)" => "(sub (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    rw!("pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"),

    rw!("mul-pow"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"),

    rw!("pow-sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" 
        if is_not_zero("?a")),

    rw!("div-pow"; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))"
        if is_gt_zero("?b")),

    rw!("div-pow-same-right"; "(div ?a (pow ?a ?b))" => "(pow ?a (sub 1 ?b))"),

    rw!("div-pow-same-left"; "(div (pow ?a ?b) ?a)" => "(pow ?a (sub ?b 1))"),

    rw!("sqrt_eq_rpow"; "(sqrt ?a)" => "(pow ?a 0.5)"),

    rw!("exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),

    rw!("mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    rw!("exp-sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),

    rw!("div-exp"; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))"),
    
    rw!("inv-exp"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),

    rw!("pow-exp"; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))"),

    rw!("log-mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log-div"; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log-exp"; "(log (exp ?a))" => "?a"),

    // NOTE(RFM): The following two rewrites are acceptable because they 
    // rewrite Props so it is not affecting the curvature of the underlying 
    // expressions.
    rw!("eq-log"; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b") 
        if not_has_log("?a") if not_has_log("?b")),

    rw!("le-log"; "(le ?a ?b)" => "(le (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b") 
        if not_has_log("?a") if not_has_log("?b")),

    // NOTE(RFM): The following rewrite is acceptable because we enforce log 
    // to only be applied once. Otherwise, we would have incompatible 
    // curvatures in the same e-class.
    rw!("map-objFun-log"; "(objFun ?a)" => "(objFun (log ?a))" 
        if is_gt_zero("?a") if not_has_log("?a")),

    
] }

pub fn example_rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_not_zero("?c")),
    
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_not_zero("?c")),
    
    rw!("inv-exp"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),
] }

#[derive(Debug)]
struct DCPScore<'a> {
    egraph: &'a EGraph,
}

impl<'a> CostFunction<Optimization> for DCPScore<'a> {
    // Curvature * term size * number of variables (with repetition).
    // In lexicographic order.
    type Cost = (Curvature, u32, u32);
    fn cost<C>(&mut self, enode: &Optimization, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        macro_rules! get_curvature {
            ($i:expr) => { costs(*$i).0 }
        }
        macro_rules! get_term_size {
            ($i:expr) => { costs(*$i).1 }
        }
        macro_rules! get_num_vars {
            ($i:expr) => { costs(*$i).2 }
        }
        
        let get_constant = 
            |i: &Id| self.egraph[*i].data.constant.clone();
        let get_domain = 
            |i: &Id| self.egraph[*i].data.domain.clone();

        let mut curvature = Curvature::Unknown;
        let mut term_size = 0;
        let mut num_vars = 0;

        match enode {
            Optimization::Prob([a, b]) => {
                curvature = 
                    if get_curvature!(b) <= get_curvature!(a) { 
                        get_curvature!(a)
                    } else if get_curvature!(a) <= get_curvature!(b) {
                        get_curvature!(b)
                    } else {
                        Curvature::Unknown
                    };
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                println!("prob: {:?} {:?} {:?}", curvature, term_size, num_vars);
            }
            Optimization::ObjFun(a) => {
                curvature = get_curvature!(a);
                term_size = 1 + get_term_size!(a);
                num_vars = get_num_vars!(a);
            }
            Optimization::Constr([h, c]) => {
                curvature = get_curvature!(c);
                term_size = 1 + get_term_size!(c);
                num_vars = get_num_vars!(c);
            }
            Optimization::Constrs(a) => {
                curvature = Curvature::Constant;
                term_size = 0;
                num_vars = 0;
                for c in a.iter() {
                    if curvature < get_curvature!(c) {
                        curvature = get_curvature!(c);
                    }
                    term_size += get_term_size!(c);
                    num_vars += get_num_vars!(c);
                }
            }
            Optimization::Eq([a, b]) => {
                curvature = 
                    if get_curvature!(a) <= Curvature::Affine && get_curvature!(b) <= Curvature::Affine {
                        Curvature::Affine
                    } else { 
                        Curvature::Unknown
                    };
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Le([a, b]) => {
                curvature = curvature::of_le(get_curvature!(a), get_curvature!(b));
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Neg(a) => {
                curvature = curvature::of_neg(get_curvature!(a));
                term_size = 1 + get_term_size!(a);
                num_vars = get_num_vars!(a);
            }
            Optimization::Sqrt(a) => {
                curvature = curvature::of_concave_fn(get_curvature!(a));
                term_size = 1 + get_term_size!(a);
                num_vars = get_num_vars!(a);
            }
            Optimization::Add([a, b]) => {
                curvature = curvature::of_add(get_curvature!(a), get_curvature!(b));
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Sub([a, b]) => {
                curvature = curvature::of_sub(get_curvature!(a), get_curvature!(b));
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Mul([a, b]) => {
                curvature = match (get_constant(a), get_constant(b)) {
                    (Some(_), Some(_)) => { 
                        Curvature::Constant
                    }
                    (Some((c1, _)), None) => {
                        curvature::of_mul_by_const(get_curvature!(b), c1.into_inner())
                    }
                    (None, Some((c2, _))) => {
                        curvature::of_mul_by_const(get_curvature!(a), c2.into_inner())
                    }
                    _ => { Curvature::Unknown }
                };
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Div([a, b]) => {
                curvature = match (get_constant(a), get_constant(b)) {
                    (Some(_), Some(_)) => { 
                        Curvature::Constant
                    }
                    (None, Some((c2, _))) => {
                        curvature::of_mul_by_const(get_curvature!(a), c2.into_inner())
                    }
                    _ => { Curvature::Unknown }
                };
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Pow([a, b]) => {
                curvature = match get_constant(b) {
                    Some((c, _)) => {
                        curvature::of_pow_by_const(get_curvature!(a), c.into_inner(), get_domain(a))
                    }
                    _ => { Curvature::Unknown }
                };
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Log(a) => {
                curvature = curvature::of_concave_fn(get_curvature!(a));
                term_size = 1 + get_term_size!(a);
                num_vars = get_num_vars!(a);
            }
            Optimization::Exp(a) => {
                curvature = curvature::of_convex_fn(get_curvature!(a));
                term_size = 1 + get_term_size!(a);
                num_vars = get_num_vars!(a);
            }
            Optimization::Var(_a) => {
                curvature = Curvature::Affine;
                term_size = 1;
                num_vars = 1;
            }
            Optimization::Param(_a) => {
                // NOTE(RFM): The story for DPP is a bit more complicated, but 
                // let's treat them as numerical constants as in DCP.
                curvature = Curvature::Constant;
                term_size = 1;
                num_vars = 0;
            }
            Optimization::Symbol(_sym) => {
                // Irrelevant.
            }
            Optimization::Constant(_f) => {
                curvature = Curvature::Constant;
                term_size = 1;
                num_vars = 0;
            }
        }

        return (curvature, term_size, num_vars);
    }
}

#[derive(Serialize, Debug)]
enum Direction {
    Forward, Backward
}

#[derive(Serialize, Debug)]
struct Step {
    rewrite_name : String,
    direction : Direction,
    expected_term : String,
}

fn get_rewrite_name_and_direction(term: &FlatTerm<Optimization>) -> Option<(String, Direction)> {
    if let Some(rule_name) = &term.backward_rule {
        return Some((rule_name.to_string(), Direction::Backward));
    }

    if let Some(rule_name) = &term.forward_rule {
        return Some((rule_name.to_string(), Direction::Forward));
    }

    if term.node.is_leaf() {
        return None
    } else {
        for child in &term.children {
            let child_res = 
                get_rewrite_name_and_direction(child);
            if child_res.is_some() {
                return child_res;
            }
        }
    };

    return None;
}

#[derive(Deserialize, Debug)]
struct Minimization {
    obj_fun : String,
    constrs : Vec<(String, String)>,
}

impl ToString for Minimization {
    fn to_string(&self) -> String {
        let obj_fun_s: String = format!("(objFun {})", self.obj_fun);
        let constrs_s_l : Vec<String> = 
            self.constrs.iter().map(|(h, c)| format!("(constr {} {})", h, c)).collect();
        let constr_s = format!("(constrs {})", constrs_s_l.join(" "));
        return format!("(prob {} {})", obj_fun_s, constr_s);
    }
}

fn get_steps(prob: Minimization, debug: bool) -> Vec<Step> {
    let prob_s = prob.to_string();
    let expr: RecExpr<Optimization> = prob_s.parse().unwrap();

    let runner = 
        Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&rules());
    
    if debug {
        println!("Creating graph with {:?} nodes.", runner.egraph.total_number_of_nodes());
        let dot_str =  runner.egraph.dot().to_string();
        fs::write("test.dot", dot_str).expect("");
    }

    let root = runner.roots[0];

    let best_cost;
    let best;
    {
        let cost_func = DCPScore { egraph: &runner.egraph };
        let extractor = 
            Extractor::new(&runner.egraph, cost_func);
        let (best_cost_found, best_found) = 
            extractor.find_best(root);
        best = best_found;
        best_cost = best_cost_found;
    }
    if debug {
        println!("Best cost: {:?}", best_cost);
        println!("Best: {:?}", best.to_string());
    }

    let mut egraph = runner.egraph;
    let mut explanation : Explanation<Optimization> = 
        egraph.explain_equivalence(&expr, &best);
    let flat_explanation : &FlatExplanation<Optimization> =
        explanation.make_flat_explanation();
    
    let mut res = Vec::new();
    if best_cost.0 <= Curvature::Convex {
        for i in 0..flat_explanation.len() {
            let expl = &flat_explanation[i];
            let expected_term = expl.get_recexpr().to_string();
            match get_rewrite_name_and_direction(expl) {
                Some((rewrite_name, direction)) => {
                    res.push(Step { rewrite_name, direction, expected_term });
                }
                None => {}
            }
        }
    }

    return res;
}

// Taken from https://github.com/opencompl/egg-tactic-code

#[derive(Deserialize, Debug)]
#[serde(tag = "request")]
enum Request {
    PerformRewrite {
        domains : Vec<(String, Domain)>,
        target : Minimization,
    }
}

#[derive(Serialize, Debug)]
#[serde(tag = "response")]
enum Response {
    Success { steps: Vec<Step> },
    Error { error: String }
}

fn main_json() -> io::Result<()> {
    env_logger::init();
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let deserializer = 
        serde_json::Deserializer::from_reader(stdin.lock());

    for read in deserializer.into_iter() {
        let response = match read {
            Err(err) => Response::Error {
                error: format!("Deserialization error: {}", err),
            },
            Ok(req) => {
                match req {
                    Request::PerformRewrite 
                        { domains, target } => 
                    Response::Success {
                        steps: get_steps(target, false)
                    }
                }
            }
        };

        serde_json::to_writer_pretty(&mut stdout, &response)?;
        println!()
    }

    Ok(())
}

fn main() {
    main_json().unwrap();
}

#[test]
fn test() {
    let s = "(le (div 1 (sqrt (var x))) (exp (var x)))".to_string();
    let s = "(add (var x) (var x))".to_string();
    // let s = "(prob 
    //     (objFun (add (add (mul (mul (div 1 (exp (var x))) (div 1 (sqrt (exp (var y))))) (div 1 (exp (var z)))) (mul (mul (div 23 10) (exp (var x))) (exp (var z)))) (mul (mul (mul 4 (exp (var x))) (exp (var y))) (exp (var z))))) 
    //     (constraints 
    //         (le (add (mul (mul (div 1 3) (div 1 (pow (exp (var x)) 2))) (div 1 (pow (exp (var y)) 2))) (mul (mul (div 4 3) (sqrt (exp (var y)))) (div 1 (exp (var z))))) 1) 
    //         (le (add (add (exp (var x)) (mul 2 (exp (var y)))) (mul 3 (exp (var z)))) 1) 
    //         (eq (mul (mul (div 1 2) (exp (var x))) (exp (var y))) 1)
    //     ))".to_string();
    let prob = Minimization {
        obj_fun : "(div 1 (div (exp (var x)) (exp (var y))))".to_string(),
        constrs : vec![
            ("h1".to_string(), "(le 2 (exp (var x)))".to_string()),
            ("h2".to_string(), "(le (exp (var x)) 3)".to_string()),
            ("h3".to_string(), "(le (add (pow (exp (var x)) 2) (div (mul 3 (exp (var y))) (exp (var z)))) (sqrt (exp (var x))))".to_string()),
            ("h4".to_string(), "(eq (div (exp (var x)) (exp (var y))) (pow (exp (var z)) 2))".to_string()),
        ]
    };
    let steps = get_steps(prob, true);
    println!("{:?}", steps);
}

