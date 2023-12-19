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

impl<'a> CostFunction<Optimization> for DCPCost<'a> {
    // Curvature + number of variables (with repetition) + term size.
    // In lexicographic order.
    type Cost = (Curvature, u32, u32);
    // Curvature analysis corresponds exactly to the DCP rules.
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
                if get_curvature!(a) <= Curvature::Affine && get_curvature!(b) <= Curvature::Affine {
                    curvature = Curvature::Affine
                }
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
            Optimization::Inv(a) => {
                let da_pos = domain::option_is_pos(get_domain(a).as_ref());
                if da_pos {
                    curvature = curvature::of_convex_nonincreasing_fn(get_curvature!(a));
                }
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Abs(a) => {
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                let da_nonpos = domain::option_is_nonpos(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_convex_nondecreasing_fn(get_curvature!(a));
                } else if da_nonpos {
                    curvature = curvature::of_convex_nonincreasing_fn(get_curvature!(a));
                } else {
                    curvature = curvature::of_convex_none_fn(get_curvature!(a));
                }
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Sqrt(a) => {
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_concave_nondecreasing_fn(get_curvature!(a));
                }
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Log(a) => {
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_concave_nondecreasing_fn(get_curvature!(a));
                }
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Exp(a) => {
                curvature = curvature::of_convex_nondecreasing_fn(get_curvature!(a));
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::XExp(a) => {
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                if da_nonneg {
                    curvature = curvature::of_convex_nondecreasing_fn(get_curvature!(a));
                }
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Entr(a) => {
                let da_pos = domain::option_is_pos(get_domain(a).as_ref());
                if da_pos {
                    curvature = curvature::of_concave_none_fn(get_curvature!(a));
                }
                num_vars = get_num_vars!(a);
                term_size = 1 + get_term_size!(a);
            }
            Optimization::Min([a, b]) => {
                let curvature_a = curvature::of_concave_nondecreasing_fn(get_curvature!(a));
                let curvature_b = curvature::of_concave_nondecreasing_fn(get_curvature!(b));
                curvature = curvature::join(curvature_a, curvature_b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Max([a, b]) => {
                let curvature_a = curvature::of_convex_nondecreasing_fn(get_curvature!(a));
                let curvature_b = curvature::of_convex_nondecreasing_fn(get_curvature!(b));
                curvature = curvature::join(curvature_a, curvature_b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Add([a, b]) => {
                curvature = curvature::of_add(get_curvature!(a), get_curvature!(b));
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
                num_vars = 1 + get_num_vars!(a) + get_num_vars!(b);
            }
            Optimization::Sub([a, b]) => {
                curvature = curvature::of_sub(get_curvature!(a), get_curvature!(b));
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Mul([a, b]) => {
                let da_o = get_domain(a);
                let db_o = get_domain(b);
                match (get_is_constant(a), get_is_constant(b)) {
                    (true, true) => { 
                        curvature = Curvature::Constant
                    }
                    (true, false) => {
                        if let Some(da) = da_o {
                            curvature = curvature::of_mul_by_const(get_curvature!(b), da)
                        }
                    }
                    (false, true) => {
                        if let Some(db) = db_o {
                            curvature = curvature::of_mul_by_const(get_curvature!(a), db)
                        }
                    }
                    _ => { }
                }
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Div([a, b]) => {
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
                                curvature = curvature::of_mul_by_const(get_curvature!(a), db)
                            }
                        }
                    }
                    _ => { }
                };   
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Pow([a, b]) => {
                if get_is_constant(b) {
                    if let Some(db) = get_domain(b) {
                        // Domain guards already in `of_pow_by_const`.
                        curvature = curvature::of_pow_by_const(get_curvature!(a), db, get_domain(a))
                    }
                } 
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::QOL([a, b]) => {
                // let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                // let da_nonpos = domain::option_is_nonpos(get_domain(a).as_ref());
                // let curvature_num = 
                //     if da_nonneg {
                //         curvature::of_convex_nondecreasing_fn(get_curvature!(a))
                //     } else if da_nonpos {
                //         curvature::of_convex_nonincreasing_fn(get_curvature!(a))
                //     } else {
                //         curvature::of_convex_none_fn(get_curvature!(a))
                //     };
                // NOTE: Aligned with the atom library.
                let curvature_num = curvature::of_convex_none_fn(get_curvature!(a));
                let db_pos = domain::option_is_pos(get_domain(b).as_ref());
                if db_pos {
                    let curvature_den = curvature::of_convex_nonincreasing_fn(get_curvature!(b));
                    curvature = curvature::join(curvature_num, curvature_den);
                }
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Geo([a, b]) => {
                let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                let db_nonneg = domain::option_is_nonneg(get_domain(b).as_ref());
                if da_nonneg && db_nonneg {
                    let curvature_a = curvature::of_concave_nondecreasing_fn(get_curvature!(a));
                    let curvature_b = curvature::of_concave_nondecreasing_fn(get_curvature!(b));
                    curvature = curvature::join(curvature_a, curvature_b);
                }
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::LSE([a, b]) => {
                let curvature_a = curvature::of_convex_nondecreasing_fn(get_curvature!(a));
                let curvature_b = curvature::of_convex_nondecreasing_fn(get_curvature!(b));
                curvature = curvature::join(curvature_a, curvature_b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
            }
            Optimization::Norm2([a, b]) => {
                // let da_nonneg = domain::option_is_nonneg(get_domain(a).as_ref());
                // let da_nonpos = domain::option_is_nonpos(get_domain(a).as_ref());
                // let curvature_a = 
                //     if da_nonneg {
                //         curvature::of_convex_nondecreasing_fn(get_curvature!(a))
                //     } else if da_nonpos {
                //         curvature::of_convex_nonincreasing_fn(get_curvature!(a))
                //     } else {
                //         curvature::of_convex_none_fn(get_curvature!(a))
                //     };
                // let db_nonneg = domain::option_is_nonneg(get_domain(b).as_ref());
                // let db_nonpos = domain::option_is_nonpos(get_domain(b).as_ref());
                // let curvature_b = 
                //     if db_nonneg {
                //         curvature::of_convex_nondecreasing_fn(get_curvature!(b))
                //     } else if db_nonpos {
                //         curvature::of_convex_nonincreasing_fn(get_curvature!(b))
                //     } else {
                //         curvature::of_convex_none_fn(get_curvature!(b))
                //     };
                // NOTE: Aligned with the atom library.
                let curvature_a = curvature::of_convex_none_fn(get_curvature!(a));
                let curvature_b = curvature::of_convex_none_fn(get_curvature!(b));
                curvature = curvature::join(curvature_a, curvature_b);
                num_vars = get_num_vars!(a) + get_num_vars!(b);
                term_size = 1 + get_term_size!(a) + get_term_size!(b);
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
