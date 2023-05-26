use egg::{rewrite as rw, *};
use core::cmp::Ordering;
use fxhash::FxHashSet as HashSet;
use ordered_float::NotNan;
use std::{fmt, io};
use serde::{Deserialize, Serialize};

pub type Constant = NotNan<f64>;

define_language! {
    pub enum Optimization {
        "prob" = Prob([Id; 2]),
        "objFun" = ObjFun(Id),
        "constraints" = Constraints(Id),
        "and" = And([Id; 2]),
        "eq" = Eq([Id; 2]),
        "le" = Le([Id; 2]),
        "neg" = Neg(Id),
        "add" = Add([Id; 2]),
        "sub" = Sub([Id; 2]),
        "mul" = Mul([Id; 2]),
        "div" = Div([Id; 2]),
        "pow" = Pow([Id; 2]),
        "log" = Log(Id),
        "exp" = Exp(Id),
        "var" = Var(Id),
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

type EGraph = egg::EGraph<Optimization, Meta>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Meta;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Curvature {
    Convex,
    Concave,
    Affine,
    Constant,
    Valid,
    Unknown,
}

impl PartialOrd for Curvature {
    fn partial_cmp(&self, other:&Curvature) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        if *self == Curvature::Convex {
            return Some(Ordering::Less);
        } 
        if *other == Curvature::Convex {
            return Some(Ordering::Greater);
        }
        if *self == Curvature::Unknown {
            return Some(Ordering::Greater);
        }
        if *other == Curvature::Unknown {
            return Some(Ordering::Less);
        }
        // NOTE(RFM): Egg unwraps this value so it cannot be None.
        return Some(Ordering::Equal);
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
            Curvature::Valid    => write!(f, "Valid"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Data {
    free_vars: HashSet<(Id, Symbol)>,
    constant: Option<(Constant, PatternAst<Optimization>)>,
    has_log: bool,
    has_exp: bool,
}

impl Analysis<Optimization> for Meta {    
    type Data = Data;
    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        to.has_exp = to.has_exp || from.has_exp;
        to.has_log = to.has_log || from.has_log;

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
        
        let mut free_vars = HashSet::default();
        let mut constant: Option<(Constant, PatternAst<Optimization>)> = None;
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
                free_vars.extend(get_vars(a));
            }
            Optimization::And([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
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
            }
            Optimization::Pow([a, b]) => {
                free_vars.extend(get_vars(a));
                free_vars.extend(get_vars(b));
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
            }
            Optimization::Exp(a) => {
                free_vars.extend(get_vars(a));
                match get_constant(a) {
                    Some((c, _)) => { 
                        constant = Some((NotNan::new(c.exp()).unwrap(), format!("(exp {})", c).parse().unwrap())); 
                    }
                    _ => {}
                }
                has_exp = true;
            }
            Optimization::Var(a) => {
                // Assume that after var there is always a symbol.
                match egraph[*a].nodes[0] { 
                    Optimization::Symbol(s) => {
                        free_vars.insert((*a, s)); 
                    }
                    _ => {}
                }
            }
            Optimization::Symbol(_) => {}
            Optimization::Constant(f) => {
                constant = Some((*f, format!("{}", f).parse().unwrap()));
            }
        }

        Data { free_vars, constant, has_log, has_exp }
    }
}

#[derive(Default)]
struct MapExp {}

impl Applier<Optimization, Meta> for MapExp {
    fn apply_one(
        &self, 
        egraph: &mut EGraph, 
        matched_id: Id, 
        _subst: &Subst, 
        _searcher_pattern: Option<&PatternAst<Optimization>>, 
        _rule_name: Symbol
    ) -> Vec<Id> {
        let free_vars : HashSet<(Id, Symbol)> = 
            egraph[matched_id].data.free_vars.clone();

        let mut res = vec![];

        for (id, sym) in free_vars {            
            if let Some((_, parent_id)) = egraph[id].parents().last() {
                if egraph[parent_id].nodes.len() > 1 {
                    continue;
                }

                // We make (var x) = (exp (var ux)).
                if egraph.are_explanations_enabled() {
                    let (new_id, did_union) = egraph.union_instantiations(
                        &format!("(var {})", sym).parse().unwrap(),
                        &format!("(exp (var u{}))", sym).parse().unwrap(),
                        &Default::default(),
                        "map-exp".to_string(),
                    );
                    if did_union {
                        egraph[new_id].nodes.retain(|n| is_exp(n));
                        res.push(parent_id);
                    }
                }
                else {
                    let y = egraph.add(Optimization::Symbol(sym));
                    let var = egraph.add(Optimization::Var(y));
                    let exp = egraph.add(Optimization::Exp(var));

                    if egraph.union(parent_id, exp) {
                        res.push(parent_id);
                    }
                }
            }
        }
        
        return res; 
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

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    // rw!("and-comm"; "(and ?a ?b)" => "(and ?b ?a)"),

    // rw!("and-assoc"; "(and (and ?a ?b) ?c)" => "(and ?a (and ?b ?c))"),
    
    rw!("eq-add"; "(eq ?a (add ?b ?c))" => "(eq (sub ?a ?c) ?b)"),

    rw!("eq-sub"; "(eq ?a (sub ?b ?c))" => "(eq (add ?a ?c) ?b)"),

    rw!("eq-mul"; "(eq ?a (mul ?b ?c))" => "(eq (div ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("eq-div"; "(eq ?a (div ?b ?c))" => "(eq (mul ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("eq-sub-zero"; "(eq ?a ?b)" => "(eq (sub ?a ?b) 0)"),

    rw!("eq-div-one"; "(eq ?a ?b)" => "(eq (div ?a ?b) 1)" 
        if is_not_zero("?b")),

    rw!("le-sub"; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)"),

    rw!("le-add"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)"),

    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("le-div"; "(le ?a (div ?b ?c))" => "(le (mul ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("le-sub-zero"; "(le ?a ?b)" => "(le (sub ?a ?b) 0)"),

    rw!("le-div-one"; "(le ?a ?b)" => "(le (div ?a ?b) 1)" 
        if is_not_zero("?b")),

    rw!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"),

    rw!("add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),

    rw!("add-0-right"; "(add ?a 0)" => "?a"),

    rw!("add-0-left"; "(add 0 ?a)" => "?a"),
    
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),

    rw!("mul-1-right"; "(mul ?a 1)" => "?a"),

    rw!("mul-1-left"; "(mul 1 ?a)" => "?a"),

    rw!("mul-0-right"; "(mul ?a 0)" => "0"),

    rw!("mul-0-left"; "(mul 0 ?a)" => "0"),

    rw!("add-sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),

    rw!("sub-add"; "(sub (add ?a ?b) ?c)" => "(add ?a (sub ?b ?c))"),

    rw!("mul-add"; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))"),

    rw!("add-mul"; "(add (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (add ?b ?c))"),

    rw!("add-mul-same"; "(add ?a (mul ?b ?a))" => "(mul ?a (add 1 ?b))"),

    rw!("mul-sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),

    rw!("sub-mul-left"; "(sub (mul ?a ?b) (mul ?a ?c))" => 
        "(mul ?a (sub ?b ?c))"),

    rw!("sub-mul-right"; "(sub (mul ?a ?b) (mul ?c ?b))" => 
        "(mul (sub ?a ?c) ?b)"),

    rw!("sub-mul-same-right"; "(sub ?a (mul ?b ?a))" => "(mul ?a (sub 1 ?b))"),

    rw!("sub-mul-same-left"; "(sub (mul ?a ?b) ?a)" => "(mul ?a (sub ?b 1))"),

    rw!("mul-div"; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)" 
        if is_not_zero("?c")),

    rw!("div-mul"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),

    rw!("div-1"; "(div ?a 1.0)" => "?a"),
    
    rw!("div-add"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    rw!("add-div"; "(add (div ?a ?b) (div ?c ?b))" => "(div (add ?a ?c) ?b)"),

    rw!("div-sub"; "(div (sub ?a ?b) ?c)" => "(sub (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    rw!("sub-div"; "(sub (div ?a ?b) (div ?c ?b))" => "(div (sub ?a ?c) ?b)"),

    rw!("sub-0"; "(sub ?a 0)" => "?a"),

    rw!("pow-1"; "(pow ?a 1)" => "?a"),

    rw!("pow-0"; "(pow ?a 0)" => "1"),

    rw!("pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"),

    rw!("mul-pow"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"),

    rw!("pow-sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" 
        if is_not_zero("?a")),

    rw!("div-pow"; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))"),

    rw!("div-pow-same-right"; "(div ?a (pow ?a ?b))" => "(pow ?a (sub 1 ?b))"),

    rw!("div-pow-same-left"; "(div (pow ?a ?b) ?a)" => "(pow ?a (sub ?b 1))"),

    rw!("exp-0"; "(exp 0)" => "1"),

    rw!("log-1"; "(log 1)" => "0"),

    rw!("exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),

    rw!("mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    rw!("exp-sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),

    rw!("div-exp"; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))"),

    rw!("pow-exp"; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))"),

    rw!("log-mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log-div"; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log-exp"; "(log (exp ?a))" => "?a"),

    rw!("eq-log"; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("le-log"; "(le ?a ?b)" => "(le (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("map-objFun-log"; "(objFun ?a)" => "(objFun (log ?a))" 
        if is_gt_zero("?a")),

    // rw!("map-domain-exp"; "(prob (objFun ?o) (constraints ?cs))" => 
    //     { MapExp {} })
]}

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

        match enode {
            Optimization::Prob([a, b]) => {
                if get_curvature(a) == Curvature::Convex && get_curvature(b) == Curvature::Valid {
                    return Curvature::Convex;
                }
                return Curvature::Unknown;
            }
            Optimization::ObjFun(a) => {
                if get_curvature(a) == Curvature::Convex || get_curvature(a) == Curvature::Affine {
                    return Curvature::Convex;
                }
                return Curvature::Unknown;
            }
            Optimization::Constraints(a) => {
                return costs(*a);
            }
            Optimization::And([a, b]) => {
                if get_curvature(a) == Curvature::Valid && get_curvature(b) == Curvature::Valid {
                    return Curvature::Valid;
                }
                return Curvature::Unknown;
            }
            Optimization::Eq([a, b]) => {
                if get_curvature(a) == Curvature::Affine && get_curvature(b) == Curvature::Affine {
                    return Curvature::Valid;
                }
                return Curvature::Unknown;
            }
            Optimization::Le([a, b]) => {
                match (get_curvature(a), get_curvature(b)) {
                    (Curvature::Convex,   Curvature::Concave)  => { return Curvature::Valid; }
                    (Curvature::Convex,   Curvature::Affine)   => { return Curvature::Valid; }
                    (Curvature::Convex,   Curvature::Constant) => { return Curvature::Valid; }
                    (Curvature::Affine,   Curvature::Concave)  => { return Curvature::Valid; }
                    (Curvature::Constant, Curvature::Concave)  => { return Curvature::Valid; }
                    (Curvature::Affine,   Curvature::Affine)   => { return Curvature::Valid; }
                    (Curvature::Constant, Curvature::Affine)   => { return Curvature::Valid; }
                    (Curvature::Affine,   Curvature::Constant) => { return Curvature::Valid; }
                    (Curvature::Constant, Curvature::Constant) => { return Curvature::Valid; }
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
                        } else {
                            return Curvature::Constant;
                        }
                        return Curvature::Unknown;
                    }
                    _ => { return Curvature::Unknown; }
                }
            }
            Optimization::Pow([_a, _b]) => {
                return Curvature::Unknown;
            }
            Optimization::Log(a) => {
                if get_curvature(a) == Curvature::Affine || get_curvature(a) == Curvature::Concave {
                    return Curvature::Concave;
                }
                if get_curvature(a) == Curvature::Constant {
                    return Curvature::Constant;
                }
                return Curvature::Unknown;
            }
            Optimization::Exp(a) => {
                if get_curvature(a) == Curvature::Affine || get_curvature(a) == Curvature::Convex {
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
            let child_res = get_rewrite_name_and_direction(child);
            if child_res.is_some() {
                return child_res;
            }
        }
    };

    return None;
}

fn get_steps(s: String) -> Vec<Step> {
    let expr: RecExpr<Optimization> = s.parse().unwrap();

    let runner = 
        Runner::default()
        .with_explanations_enabled()
        .with_expr(&expr)
        .run(&rules());
    
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

    let mut egraph = runner.egraph;
    let mut explanation : Explanation<Optimization> = 
        egraph.explain_equivalence(&expr, &best);
    let flat_explanation : &FlatExplanation<Optimization> =
        explanation.make_flat_explanation();
    
    let mut res = Vec::new();
    if best_cost == Curvature::Convex {
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
                    Request::PerformRewrite { target } => 
                    Response::Success {
                        steps: get_steps(target)
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
