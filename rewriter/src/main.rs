use egg::{rewrite as rw, *};
use core::cmp::Ordering;
use std::collections::HashMap;
use fxhash::FxHashSet as HashSet;
use ordered_float::NotNan;
use std::{fs, fmt, io};
use serde::{Deserialize, Serialize};

pub type Constant = NotNan<f64>;

define_language! {
    pub enum Optimization {
        "prob" = Prob([Id; 2]),
        "objFun" = ObjFun(Id),
        "constraints" = Constraints(Box<[Id]>),
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

fn is_exp(opt: &Optimization) -> bool {
    match opt {
        Optimization::Exp(_) => true,
        _ => false,
    }
}

// TODO(RFM): Factor out.
#[derive(Debug, Copy, Clone, Deserialize, PartialEq, Eq)]
pub enum Domain {
    Free,
    NonNeg,
    NonPos,
    Pos,
    Neg,
    Zero,
    PosConst,
    NegConst
}
/*
           Free
          /    \
     NonNeg    NonPos
       |   \  /   |
      Pos  Zero  Neg
       |          |
    PosConst   NegConst
 */
impl PartialOrd for Domain {
    fn partial_cmp(&self, other:&Domain) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        match (*self, *other) {
            (Domain::Free,     _               ) => { return Some(Ordering::Greater); }
            (_,                Domain::Free    ) => { return Some(Ordering::Less);    }
            (Domain::NonNeg,   Domain::Pos     ) => { return Some(Ordering::Greater); }
            (Domain::Pos,      Domain::NonNeg  ) => { return Some(Ordering::Less);    }
            (Domain::NonNeg,   Domain::Zero    ) => { return Some(Ordering::Greater); }
            (Domain::Zero,     Domain::NonNeg  ) => { return Some(Ordering::Less);    }
            (Domain::Pos,      Domain::PosConst) => { return Some(Ordering::Greater); }
            (Domain::PosConst, Domain::Pos     ) => { return Some(Ordering::Less);    }
            (Domain::NonPos,   Domain::Neg     ) => { return Some(Ordering::Greater); }
            (Domain::Neg,      Domain::NonPos  ) => { return Some(Ordering::Less);    }
            (Domain::NonPos,   Domain::Zero    ) => { return Some(Ordering::Greater); }
            (Domain::Zero,     Domain::NonPos  ) => { return Some(Ordering::Less);    }
            (Domain::Neg,      Domain::NegConst) => { return Some(Ordering::Greater); }
            (Domain::NegConst, Domain::Neg     ) => { return Some(Ordering::Less);    }
            _ => { return None; }
        }
    }
}

fn domain_is_free(d:Domain) -> bool {
    return d == Domain::Free;
}

fn domain_is_zero(d:Domain) -> bool {
    return d == Domain::Zero;
}

fn domain_is_pos(d:Domain) -> bool {
    return d == Domain::Pos || d == Domain::PosConst;
}

fn domain_is_neg(d:Domain) -> bool {
    return d == Domain::Neg || d == Domain::NegConst;
}

fn domain_is_nonneg(d:Domain) -> bool {
    return d == Domain::NonNeg || d == Domain::Zero || domain_is_pos(d);
}

fn domain_is_nonpos(d:Domain) -> bool {
    return d == Domain::NonPos || d == Domain::Zero || domain_is_neg(d);
}

fn domain_flip(d:Domain) -> Domain {
    match d {
        Domain::Free     => { return Domain::Free;     }
        Domain::NonNeg   => { return Domain::NonPos;   }
        Domain::NonPos   => { return Domain::NonNeg;   }
        Domain::Pos      => { return Domain::Neg;      }
        Domain::Neg      => { return Domain::Pos;      }
        Domain::Zero     => { return Domain::Zero;     }
        Domain::PosConst => { return Domain::NegConst; }
        Domain::NegConst => { return Domain::PosConst; }
    }
}

fn domain_option_flip(d:Option<Domain>) -> Option<Domain> {
    return d.map(domain_flip);
}

fn domain_union(d_a:Domain, d_b:Domain) -> Domain {
    match (d_a, d_b) {
        (Domain::Zero, Domain::Pos ) => { return Domain::NonNeg; }
        (Domain::Pos,  Domain::Zero) => { return Domain::NonNeg; }
        (Domain::Zero, Domain::Neg ) => { return Domain::NonPos; }
        (Domain::Neg,  Domain::Zero) => { return Domain::NonPos; }
        _ => {
            match d_a.partial_cmp(&d_b) {
                Some(Ordering::Equal)   => { return d_a; }
                Some(Ordering::Less)    => { return d_b; }
                Some(Ordering::Greater) => { return d_a; }
                _                       => { return Domain::Free; }
            }
        }
    }
}

// TODO(RFM): Move.
pub fn option_map2<T1, T2, U, F>(x1: Option<T1>, x2: Option<T2>, f: F) -> Option<U>
    where
        F: FnOnce(T1, T2) -> U,
    {
        match (x1, x2) {
            (Some(x1_val), Some(x2_val)) => { 
                return Some(f(x1_val, x2_val)); 
            }
            _ => { return None; }
        }
    }

fn domain_option_union(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    return option_map2(d_o_a, d_o_b, domain_union);
}

fn domain_add(d_a:Domain, d_b:Domain) -> Domain {
    match (d_a, d_b) {
        (Domain::Zero,   _             ) => { return d_b; }
        (_,              Domain::Zero  ) => { return d_a; }
        (Domain::NonNeg, Domain::Pos   ) => { return Domain::Pos; }
        (Domain::Pos,    Domain::NonNeg) => { return Domain::Pos; }
        (Domain::NonPos, Domain::Neg   ) => { return Domain::Neg; }
        (Domain::Neg,    Domain::NonPos) => { return Domain::Neg; }
        _ => { return domain_union(d_a, d_b); }
    }
}

fn domain_option_add(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    return option_map2(d_o_a, d_o_b, domain_add);
}

fn domain_mul(d_a:Domain, d_b:Domain) -> Domain {
    if domain_is_zero(d_a) || domain_is_zero(d_b) {
        return Domain::Zero;
    } else if domain_is_free(d_a) || domain_is_free(d_b) {
        return Domain::Free;
    } else if domain_is_nonneg(d_a) && domain_is_nonneg(d_b) {
        return domain_add(d_a, d_b);
    } else if domain_is_nonpos(d_a) && domain_is_nonpos(d_b) {
        return domain_add(d_a, d_b);
    } else {
        // Opposite sign case.
        if domain_is_neg(d_a) {
            return domain_flip(d_b);
        } else if domain_is_neg(d_b) {
            return domain_flip(d_a);
        } else {
            return Domain::Free;
        }
    }
}

fn domain_option_mul(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    return option_map2(d_o_a, d_o_b, domain_mul);
}

type EGraph = egg::EGraph<Optimization, Meta>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Meta {
    domain : Vec<(Symbol, Domain)>,
}

// TODO(RFM): Remove "Valid", split Real and Prop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Curvature {
    Convex,
    Concave,
    Affine,
    Constant,
    Unknown,
}

/*
        Unknown 
        /     \ 
    Convex   Concave
        \     /
         Affine
           |
        Constant
 */
impl PartialOrd for Curvature {
    fn partial_cmp(&self, other:&Curvature) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        // Constant < Non-constant.
        if *self == Curvature::Constant {
            return Some(Ordering::Less);
        } 
        // Non-constant > Constant.
        if *other == Curvature::Constant {
            return Some(Ordering::Greater);
        }
        // Affine < Non-affine.
        if *self == Curvature::Affine {
            return Some(Ordering::Less);
        }
        // Non-affine > Affine.
        if *other == Curvature::Affine {
            return Some(Ordering::Greater);
        }
        // Convex < Unknown.
        if *self == Curvature::Convex && *other == Curvature::Unknown {
            return Some(Ordering::Less);
        }
        // Unknown > Convex.
        if *self == Curvature::Unknown && *other == Curvature::Convex {
            return Some(Ordering::Greater);
        }
        // Concave < Unknown.
        if *self == Curvature::Concave && *other == Curvature::Unknown {
            return Some(Ordering::Less);
        }
        // Unknown > Concave.
        if *self == Curvature::Unknown && *other == Curvature::Concave {
            return Some(Ordering::Greater);
        }

        return None;
    }
}

impl fmt::Display for Curvature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Curvature::Convex   => write!(f, "Convex"),
            Curvature::Concave  => write!(f, "Concave"),
            Curvature::Affine   => write!(f, "Affine"),
            Curvature::Unknown  => write!(f, "Unknown"),
            Curvature::Constant => write!(f, "Constant"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Data {
    free_vars: HashSet<(Id, Symbol)>,
    domain: Option<Domain>,
    constant: Option<(Constant, PatternAst<Optimization>)>,
    has_log: bool,
    has_exp: bool,
}

impl Analysis<Optimization> for Meta {    
    type Data = Data;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        to.has_exp = to.has_exp || from.has_exp;
        to.has_log = to.has_log || from.has_log;

        match (to.domain, from.domain) {
            (None, Some(_)) => { to.domain = from.domain; }
            (Some(d_to), Some(d_from)) => {
                if d_to != d_from { to.domain = None; }
            }
            _ => ()
        }

        let before_len = to.free_vars.len();
        to.free_vars.retain(|i| from.free_vars.contains(i));
        
        DidMerge(
            before_len != to.free_vars.len(),
            to.free_vars.len() != from.free_vars.len(),
        )
    }

    fn make(egraph: &EGraph, enode: &Optimization) -> Self::Data {
        let get_vars = 
            |i: &Id| egraph[*i].data.free_vars.iter().cloned();
        let get_constant = 
            |i: &Id| egraph[*i].data.constant.clone();
        let get_domain = 
            |i: &Id| egraph[*i].data.domain.clone();
        let var_map : HashMap<Symbol, Domain> = 
            egraph.analysis.domain.clone().into_iter().collect();

        let mut free_vars = HashSet::default();
        let mut constant = None;
        let mut domain = None;
        let mut has_log = false;
        let mut has_exp = false;

        match enode {
            Optimization::Prob([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
            }
            Optimization::ObjFun(a) => {
                free_vars.extend(get_vars(a));
                
            }
            Optimization::Constraints(a) => {
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
                domain = domain_option_flip(get_domain(a));
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
                        if domain_is_nonneg(d_a) {
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

                domain = domain_option_add(
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
                domain = domain_option_add(
                    get_domain(a), 
                    domain_option_flip(get_domain(b)));
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
                domain = domain_option_mul(
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
                        if domain_is_pos(d_b) || domain_is_neg(d_b) {
                            domain = domain_option_mul(
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
                        if !domain_is_zero(d_a) && domain_is_zero(d_b) {
                            // NOTE(RFM): This is technically 1.
                            domain = Some(Domain::PosConst);
                        } else if domain_is_pos(d_a) {
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
                        if domain_is_pos(d_a) {
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
                has_exp = true;

                domain = Some(Domain::Pos);
            }
            Optimization::Var(a) => {
                // Assume that after var there is always a symbol.
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        free_vars.insert((*a, s)); 
                        match var_map.get(&s) {
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

        Data { free_vars, constant, domain, has_log, has_exp }
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

    // NOTE(RFM): Turn all rws above into a normalization step? 

    rw!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"), 

    rw!("add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
    
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),

    rw!("add-sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),

    rw!("add-mul"; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))"),

    //rw!("mul-sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),

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

    //rw!("div-mul"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),
    
    rw!("div-add"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    //rw!("add-div"; "(add (div ?a ?b) (div ?c ?b))" => "(div (add ?a ?c) ?b)"),

    rw!("div-sub"; "(div (sub ?a ?b) ?c)" => "(sub (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    rw!("pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"),

    //rw!("mul-pow"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"),

    rw!("pow-sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" 
        if is_not_zero("?a")),

    rw!("div-pow"; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))"
        if is_gt_zero("?b")),

    rw!("div-pow-same-right"; "(div ?a (pow ?a ?b))" => "(pow ?a (sub 1 ?b))"),

    rw!("div-pow-same-left"; "(div (pow ?a ?b) ?a)" => "(pow ?a (sub ?b 1))"),

    rw!("sqrt_eq_rpow"; "(sqrt ?a)" => "(pow ?a 0.5)"),

    //rw!("exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),

    rw!("mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    //rw!("exp-sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),

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
    type Cost = Curvature;
    fn cost<C>(&mut self, enode: &Optimization, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        let mut get_curvature =
            |i: &Id| costs(*i);
        let get_constant = 
            |i: &Id| self.egraph[*i].data.constant.clone();
        let get_domain = 
            |i: &Id| self.egraph[*i].data.domain.clone();

        match enode {
            Optimization::Prob([a, b]) => {
                if get_curvature(b) <= get_curvature(a) {
                    return get_curvature(a);
                }
                else if get_curvature(a) <= get_curvature(b) {
                    return get_curvature(b);
                }
                return Curvature::Unknown;
            }
            Optimization::ObjFun(a) => {
                return get_curvature(a);
            }
            Optimization::Constraints(a) => {
                let mut curvature = Curvature::Constant;
                for c in a.iter() {
                    if curvature < costs(*c) {
                        curvature = costs(*c);
                        break;
                    }
                }
                return curvature;
            }
            Optimization::Eq([a, b]) => {
                if get_curvature(a) <= Curvature::Affine && get_curvature(b) <= Curvature::Affine {
                    return Curvature::Affine;
                }
                return Curvature::Unknown;
            }
            Optimization::Le([a, b]) => {
                match (get_curvature(a), get_curvature(b)) {
                    (Curvature::Convex,   Curvature::Concave)  => { return Curvature::Convex; }
                    (Curvature::Convex,   Curvature::Affine)   => { return Curvature::Convex; }
                    (Curvature::Convex,   Curvature::Constant) => { return Curvature::Convex; }
                    (Curvature::Affine,   Curvature::Concave)  => { return Curvature::Convex; }
                    (Curvature::Constant, Curvature::Concave)  => { return Curvature::Convex; }
                    (Curvature::Affine,   Curvature::Affine)   => { return Curvature::Affine; }
                    (Curvature::Constant, Curvature::Affine)   => { return Curvature::Affine; }
                    (Curvature::Affine,   Curvature::Constant) => { return Curvature::Affine; }
                    (Curvature::Constant, Curvature::Constant) => { return Curvature::Constant; }
                    _ => { return Curvature::Unknown; }
                } 
            }
            Optimization::Neg(a) => {
                match get_curvature(a) {
                    Curvature::Convex   => { return Curvature::Concave; }
                    Curvature::Concave  => { return Curvature::Convex; }
                    Curvature::Affine   => { return Curvature::Affine; }
                    Curvature::Constant => { return Curvature::Constant; }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Sqrt(a) => {
                match get_curvature(a) {
                    Curvature::Convex   => { return Curvature::Unknown; }
                    Curvature::Concave  => { return Curvature::Concave; }
                    Curvature::Affine   => { return Curvature::Concave; }
                    Curvature::Constant => { return Curvature::Concave; }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Add([a, b]) => {
                match (get_curvature(a), get_curvature(b)) {
                    (Curvature::Convex,   Curvature::Convex)   => { return Curvature::Convex; }
                    (Curvature::Convex,   Curvature::Affine)   => { return Curvature::Convex; }
                    (Curvature::Convex,   Curvature::Constant) => { return Curvature::Convex; }
                    (Curvature::Affine,   Curvature::Convex)   => { return Curvature::Convex; }
                    (Curvature::Constant, Curvature::Convex)   => { return Curvature::Convex; }

                    (Curvature::Concave,  Curvature::Concave)  => { return Curvature::Concave; }
                    (Curvature::Concave,  Curvature::Affine)   => { return Curvature::Concave; }
                    (Curvature::Concave,  Curvature::Constant) => { return Curvature::Concave; }
                    (Curvature::Affine,   Curvature::Concave)  => { return Curvature::Concave; }
                    (Curvature::Constant, Curvature::Concave)  => { return Curvature::Concave; }

                    (Curvature::Affine,   Curvature::Affine)   => { return Curvature::Affine; }
                    (Curvature::Affine,   Curvature::Constant) => { return Curvature::Affine; }
                    (Curvature::Constant, Curvature::Affine)   => { return Curvature::Affine; }

                    (Curvature::Constant, Curvature::Constant) => { return Curvature::Constant; }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Sub([a, b]) => {
                match (get_curvature(a), get_curvature(b)) {
                    (Curvature::Convex,   Curvature::Concave)  => { return Curvature::Convex; }
                    (Curvature::Convex,   Curvature::Affine)   => { return Curvature::Convex; }
                    (Curvature::Convex,   Curvature::Constant) => { return Curvature::Convex; }
                    (Curvature::Affine,   Curvature::Concave)  => { return Curvature::Convex; }
                    (Curvature::Constant, Curvature::Concave)  => { return Curvature::Convex; }

                    (Curvature::Concave,  Curvature::Convex)   => { return Curvature::Concave; }
                    (Curvature::Concave,  Curvature::Affine)   => { return Curvature::Concave; }
                    (Curvature::Concave,  Curvature::Constant) => { return Curvature::Concave; }
                    (Curvature::Affine,   Curvature::Convex)   => { return Curvature::Concave; }
                    (Curvature::Constant, Curvature::Convex)   => { return Curvature::Concave; }

                    (Curvature::Affine,   Curvature::Affine)   => { return Curvature::Affine; }
                    (Curvature::Affine,   Curvature::Constant) => { return Curvature::Affine; }
                    (Curvature::Constant, Curvature::Affine)   => { return Curvature::Affine; }

                    (Curvature::Constant, Curvature::Constant) => { return Curvature::Constant; }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Mul([a, b]) => {
                match (get_constant(a), get_constant(b)) {
                    (Some(_), Some(_)) => { 
                        return Curvature::Constant;
                    }
                    (Some((c1, _)), None) => {
                        if c1.into_inner() < 0.0 {
                            if get_curvature(b) == Curvature::Concave {
                                return Curvature::Convex;
                            } else if get_curvature(b) == Curvature::Convex {
                                return Curvature::Concave;
                            } else if get_curvature(b) == Curvature::Affine {
                                return Curvature::Affine;
                            }
                        } else if c1.into_inner() > 0.0 {
                            if get_curvature(b) == Curvature::Concave {
                                return Curvature::Concave;
                            } else if get_curvature(b) == Curvature::Convex {
                                return Curvature::Convex;
                            } else if get_curvature(b) == Curvature::Affine {
                                return Curvature::Affine;
                            }
                        } else {
                            return Curvature::Constant;
                        }
                        return Curvature::Unknown;
                    }
                    (None, Some((c2, _))) => {
                        if c2.into_inner() < 0.0 {
                            if get_curvature(a) == Curvature::Concave {
                                return Curvature::Convex;
                            } else if get_curvature(a) == Curvature::Convex {
                                return Curvature::Concave;
                            } else if get_curvature(a) == Curvature::Affine {
                                return Curvature::Affine;
                            }
                        } else if c2.into_inner() > 0.0 {
                            if get_curvature(a) == Curvature::Concave {
                                return Curvature::Concave;
                            } else if get_curvature(a) == Curvature::Convex {
                                return Curvature::Convex;
                            } else if get_curvature(a) == Curvature::Affine {
                                return Curvature::Affine;
                            }
                        } else {
                            return Curvature::Constant;
                        }
                        return Curvature::Unknown;
                    }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Div([a, b]) => {
                match (get_constant(a), get_constant(b)) {
                    (Some(_), Some(_)) => { 
                        return Curvature::Constant;
                    }
                    (None, Some((c2, _))) => {
                        if c2.into_inner() < 0.0 {
                            if get_curvature(a) == Curvature::Concave {
                                return Curvature::Convex;
                            } else if get_curvature(a) == Curvature::Convex {
                                return Curvature::Concave;
                            } else if get_curvature(a) == Curvature::Affine {
                                return Curvature::Affine;
                            }
                        } else if c2.into_inner() > 0.0 {
                            if get_curvature(a) == Curvature::Concave {
                                return Curvature::Concave;
                            } else if get_curvature(a) == Curvature::Convex {
                                return Curvature::Convex;
                            } else if get_curvature(a) == Curvature::Affine {
                                return Curvature::Affine;
                            }
                        } 
                        return Curvature::Unknown;
                    }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Pow([a, b]) => {
                match get_constant(b) {
                    Some((c, _)) => {
                        match get_curvature(a) {
                            Curvature::Constant => { 
                                return Curvature::Constant;
                            }
                            Curvature::Affine => {
                                let c_val = c.into_inner();
                                if c_val == 0.0 {
                                    return Curvature::Constant;
                                } else if c_val == 1.0 {
                                    return Curvature::Affine;
                                } else if c_val < 0.0 {
                                    // NOTE(RFM): Not 100% correct, convex if x > 0 otherwise unknown.
                                    return Curvature::Convex;
                                } else if 0.0 < c_val && c_val < 1.0 {
                                    // NOTE(RFM): Not 100% correct, convex if x >= 0 otherwise unknown.
                                    return Curvature::Concave;
                                } else if 
                                    c_val == (c_val as u32) as f64 && 
                                    (c_val as u32) % 2 == 0 {
                                    return Curvature::Convex;
                                } else {
                                    // NOTE(RFM): Not 100% correct, convex if x >= 0 otherwise unknown.
                                    return Curvature::Convex;
                                }
                            }
                            _ => { return Curvature::Unknown; }
                        }
                    }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Log(a) => {
                if get_curvature(a) == Curvature::Affine {
                    return Curvature::Concave;
                }
                if get_curvature(a) == Curvature::Constant {
                    return Curvature::Constant;
                }
                return Curvature::Unknown;
            }
            Optimization::Exp(a) => {
                if get_curvature(a) == Curvature::Affine {
                    return Curvature::Convex;
                }
                if get_curvature(a) == Curvature::Constant {
                    return Curvature::Constant;
                }
                return Curvature::Unknown;
            }
            Optimization::Var(_a) => {
                return Curvature::Affine;
            }
            Optimization::Param(_a) => {
                // NOTE(RFM): The story for DPP is a bit more complicated, but 
                // let's treat them as numerical constants as in DCP.
                return Curvature::Constant;
            }
            Optimization::Symbol(_sym) => {
                // Irrelevant.
                return Curvature::Unknown;
            }
            Optimization::Constant(_f) => {
                return Curvature::Constant;
            }
        }
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

fn get_steps(s: String, debug: bool) -> Vec<Step> {
    let expr: RecExpr<Optimization> = s.parse().unwrap();

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
    if best_cost <= Curvature::Convex {
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
        target : String,
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
    let s = "(prob 
        (objFun (add (add (mul (mul (div 1 (exp (var x))) (div 1 (sqrt (exp (var y))))) (div 1 (exp (var z)))) (mul (mul (div 23 10) (exp (var x))) (exp (var z)))) (mul (mul (mul 4 (exp (var x))) (exp (var y))) (exp (var z))))) 
        (constraints 
            (le (add (mul (mul (div 1 3) (div 1 (pow (exp (var x)) 2))) (div 1 (pow (exp (var y)) 2))) (mul (mul (div 4 3) (sqrt (exp (var y)))) (div 1 (exp (var z))))) 1) 
            (le (add (add (exp (var x)) (mul 2 (exp (var y)))) (mul 3 (exp (var z)))) 1) 
            (eq (mul (mul (div 1 2) (exp (var x))) (exp (var y))) 1)
        ))".to_string();
    let steps = get_steps(s, true);
    println!("{:?}", steps);
}

