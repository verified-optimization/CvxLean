use egg::{*};

use crate::domain;
use domain::Domain as Domain;

use crate::curvature;
use curvature::Curvature as Curvature;

use crate::optimization;
use optimization::Optimization as Optimization;

#[derive(Debug)]
pub struct DCPCost<'a> {
    pub egraph: &'a optimization::EGraph,
}

impl<'a> CostFunction<Optimization> for DCPCost<'a> {
    // Curvature + number of variables (with repetition) + term size.
    // In lexicographic order.
    type Cost = (Curvature, u32, u32);
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
        
        let get_domain = 
            |i: &Id| self.egraph[*i].data.domain.clone();

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
                curvature = curvature::of_concave_fn(get_curvature!(a));
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
                let ca_o = Domain::option_get_constant(get_domain(a));
                let cb_o = Domain::option_get_constant(get_domain(b));
                curvature = match (ca_o, cb_o) {
                    (Some(_), Some(_)) => { 
                        Curvature::Constant
                    }
                    (Some(ca), None) => {
                        curvature::of_mul_by_const(get_curvature!(b), ca)
                    }
                    (None, Some(cb)) => {
                        curvature::of_mul_by_const(get_curvature!(a), cb)
                    }
                    _ => { Curvature::Unknown }
                };
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Div([a, b]) => {
                let ca_o = Domain::option_get_constant(get_domain(a));
                let cb_o = Domain::option_get_constant(get_domain(b));
                curvature = match (ca_o, cb_o) {
                    (Some(_), Some(cb)) => {
                        if cb == 0.0 {
                            Curvature::Unknown
                        } else {
                            Curvature::Constant
                        }
                    }
                    (None, Some(cb)) => {
                        curvature::of_mul_by_const(get_curvature!(a), cb)
                    }
                    _ => { Curvature::Unknown }
                };
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Pow([a, b]) => {
                let cb_o = Domain::option_get_constant(get_domain(b));
                curvature = match cb_o {
                    Some(cb) => {
                        curvature::of_pow_by_const(get_curvature!(a), cb, get_domain(a))
                    }
                    _ => { Curvature::Unknown }
                };
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Log(a) => {
                curvature = curvature::of_concave_fn(get_curvature!(a));
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Exp(a) => {
                curvature = curvature::of_convex_fn(get_curvature!(a));
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

        return (curvature, num_vars, term_size);
    }
}
