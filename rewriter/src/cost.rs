use std::cmp::Ordering;

use egg::{*};

use crate::domain;

use crate::curvature;
use curvature::Curvature as Curvature;

use crate::optimization;
use optimization::Optimization as Optimization;

#[derive(Debug)]
pub struct DCPCost<'a> {
    pub egraph: &'a optimization::EGraph,
}

#[derive(Debug, Clone, PartialEq)]
pub struct OptimizationWrapper(Optimization);

impl PartialOrd for OptimizationWrapper {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ordering::Equal)
    }
}

impl<'a> CostFunction<Optimization> for DCPCost<'a> {
    // Curvature + number of variables (with repetition) + term size.
    // In lexicographic order.
    type Cost = (Curvature, u32, u32, OptimizationWrapper);
    fn cost<C>(&mut self, enode: &Optimization, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        macro_rules! get_curvature {
            ($i:expr) => { costs(*$i).0 }
        }
        macro_rules! get_num_vars {
            ($i:expr) => { costs(*$i).1 }
        }
        macro_rules! get_term_size {
            ($i:expr) => { costs(*$i).2 }
        }
        macro_rules! get_node {
            ($i:expr) => { costs(*$i).3 }
        }
        
        let get_domain = 
            |i: &Id| self.egraph[*i].data.domain.clone();
        
        let get_is_constant = 
            |i: &Id| self.egraph[*i].data.is_constant.clone();

        let mut curvature = Curvature::Unknown;
        let mut num_vars = 0;
        let mut term_size = 0;
        
        match enode {
            Optimization::Prob([a, b]) => {
                curvature = 
                    if get_curvature!(a) >= get_curvature!(b) {
                        get_curvature!(a)
                    } else if get_curvature!(b) >= get_curvature!(a) {
                        get_curvature!(b)
                    } else {
                        // Should not get here.
                        Curvature::Unknown
                    };
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::ObjFun(a) => {
                // It cannot be concave, because of mapping functions.
                curvature = 
                    if get_curvature!(a) <= Curvature::Convex {
                        get_curvature!(a)
                    } else {
                        Curvature::Unknown
                    };
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Constr([_, c]) => {
                // It cannot be concave, because the notion of concavity at the
                // prop (or set) level is not well-defined.
                curvature = 
                    if get_curvature!(c) <= Curvature::Convex {
                        get_curvature!(c)
                    } else {
                        Curvature::Unknown
                    };
                num_vars = get_num_vars!(c);
                term_size = 1 + get_term_size!(c);
            }
            Optimization::Constrs(a) => {
                curvature = Curvature::Constant;
                term_size = 0;
                num_vars = 0;
                for c in a.iter() {
                    if curvature < get_curvature!(c) {
                        curvature = get_curvature!(c);
                    }
                    num_vars += get_num_vars!(c);
                    term_size += get_term_size!(c);
                }
            }
            Optimization::Eq([a, b]) => {
                curvature = 
                    if get_curvature!(a) <= Curvature::Affine && get_curvature!(b) <= Curvature::Affine {
                        Curvature::Affine
                    } else { 
                        Curvature::Unknown
                    };
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Le([a, b]) => {
                curvature = curvature::of_le(get_curvature!(a), get_curvature!(b));
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Neg(a) => {
                curvature = curvature::of_neg(get_curvature!(a));
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Sqrt(a) => {
                // TODO: Temporary. geo_mean.
                let mut is_geo_mean = false;
                match get_node!(a).0 {
                    Optimization::Mul([b, c]) => {
                        let affine = 
                            get_curvature!(&b) == Curvature::Affine && 
                            get_curvature!(&c) == Curvature::Affine;
                        let pos =
                            domain::option_is_pos(get_domain(&b).as_ref()) && 
                            domain::option_is_pos(get_domain(&c).as_ref());
                        is_geo_mean = affine && pos;
                    }
                    _ => {}
                }
                // TODO: Temporary. norm2.
                let mut is_norm2 = false; 
                match get_node!(a).0 {
                    Optimization::Add([b, c]) => {
                        match (get_node!(&b).0, get_node!(&c).0) {
                            (Optimization::Pow([d, e]), Optimization::Pow([f, g])) => {
                                let curvature_check = 
                                    get_curvature!(&d) <= Curvature::Convex && 
                                    get_curvature!(&f) <= Curvature::Convex;
                                let pow_two_first = 
                                    match get_domain(&e) {
                                        Some(de) => 
                                            match domain::Domain::get_constant(&de) {
                                                Some (de_f) => de_f == 2.0,
                                                _ => false
                                            }
                                        _ => false 
                                    };
                                let pow_two_second =
                                    match get_domain(&g) {
                                        Some(dg) => 
                                            match domain::Domain::get_constant(&dg) {
                                                Some (dg_f) => dg_f == 2.0,
                                                _ => false
                                            }
                                        _ => false 
                                    };
                                is_norm2 = curvature_check && pow_two_first && pow_two_second;
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
                if is_geo_mean || is_norm2 {
                    curvature = Curvature::Convex;
                } else {
                    curvature = curvature::of_concave_increasing_fn(get_curvature!(a));
                }
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Add([a, b]) => {
                curvature = curvature::of_add(get_curvature!(a), get_curvature!(b));
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Sub([a, b]) => {
                curvature = curvature::of_sub(get_curvature!(a), get_curvature!(b));
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Mul([a, b]) => {
                let da_o = get_domain(a);
                let db_o = get_domain(b);
                curvature = match (get_is_constant(a), get_is_constant(b)) {
                    (true, true) => { 
                        Curvature::Constant
                    }
                    (true, false) => {
                        match da_o {
                            Some(da) => {
                                curvature::of_mul_by_const(get_curvature!(b), da)
                            }
                            None => { Curvature::Unknown }
                        }
                    }
                    (false, true) => {
                        match db_o {
                            Some(db) => {
                                curvature::of_mul_by_const(get_curvature!(a), db)
                            }
                            None => { Curvature::Unknown }
                        }
                    }
                    _ => { Curvature::Unknown }
                };
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Div([a, b]) => {
                // TODO: Temporary. quad_over_lin.
                let mut is_quad_over_lin = false;
                match get_node!(a).0 {
                    Optimization::Pow([c, d]) => {
                        let curvature_check = 
                            get_curvature!(b) <= Curvature::Concave && 
                            get_curvature!(&c) <= Curvature::Affine && 
                            get_curvature!(&d) == Curvature::Constant;
                        let pos_check =
                            domain::option_is_pos(get_domain(&b).as_ref());
                        let pow_two_check = 
                            match get_domain(&d) {
                                Some(dd) => 
                                    match domain::Domain::get_constant(&dd) {
                                        Some (dd_f) => dd_f == 2.0,
                                        _ => false
                                    }
                                _ => false 
                            };
                        is_quad_over_lin = curvature_check && pos_check && pow_two_check;
                    }
                    _ => {}
                }

                if is_quad_over_lin {
                    println!("quad_over_lin");
                    curvature = Curvature::Convex;
                } else {
                    let db_o = get_domain(b);
                    curvature = match (get_is_constant(a), get_is_constant(b)) {
                        (true, true) => {
                            match db_o {
                                Some(db) => {
                                    if domain::does_not_contain_zero(&db) {
                                        Curvature::Constant
                                    } else {
                                        Curvature::Unknown
                                    }
                                    
                                }
                                None => { Curvature::Unknown }
                            }
                        }
                        (false, true) => {
                            match db_o {
                                Some(db) => {
                                    if domain::does_not_contain_zero(&db) {
                                        curvature::of_mul_by_const(get_curvature!(a), db)
                                    } else {
                                        Curvature::Unknown
                                    }
                                }
                                None => { Curvature::Unknown }
                            }
                        }
                        _ => { Curvature::Unknown }
                    };   
                }
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Pow([a, b]) => {
                curvature = if get_is_constant(b) {
                    match get_domain(b) {
                        Some(db) => {
                            curvature::of_pow_by_const(get_curvature!(a), db, get_domain(a))
                        }
                        _ => { Curvature::Unknown }
                    }
                } else { Curvature::Unknown };
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Log(a) => {
                curvature = curvature::of_concave_increasing_fn(get_curvature!(a));
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Exp(a) => {
                curvature = curvature::of_convex_increasing_fn(get_curvature!(a));
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Var(_a) => {
                curvature = Curvature::Affine;
                num_vars = 1;
                term_size = 1;
            }
            Optimization::Param(_a) => {
                // NOTE: The story for DPP is a bit more complicated, but 
                // let's treat them as numerical constants as in DCP.
                curvature = Curvature::Constant;
                num_vars = 0;
                term_size = 1;
            }
            Optimization::Symbol(_sym) => {
                // Irrelevant.
            }
            Optimization::Constant(_f) => {
                curvature = Curvature::Constant;
                num_vars = 0;
                term_size = 1;
            }
        }

        return (curvature, num_vars, term_size, OptimizationWrapper(enode.clone()));
    }

}
