use egg::{*};

use crate::curvature;
use curvature::Curvature as Curvature;

use crate::optimization;
use optimization::Optimization as Optimization;

#[derive(Debug)]
pub struct DCPCost<'a> {
    egraph: &'a optimization::EGraph,
}

impl<'a> CostFunction<Optimization> for DCPCost<'a> {
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
