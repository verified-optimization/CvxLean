use core::cmp::Ordering;
use std::fmt;

use crate::domain;
use domain::Domain as Domain;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Curvature {
    Unknown,
    Convex,
    Concave,
    Affine,
    Constant,
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
            Curvature::Unknown  => write!(f, "Unknown"),
            Curvature::Convex   => write!(f, "Convex"),
            Curvature::Concave  => write!(f, "Concave"),
            Curvature::Affine   => write!(f, "Affine"),
            Curvature::Constant => write!(f, "Constant"),
        }
    }
}

pub fn of_le(c1: Curvature, c2: Curvature) -> Curvature {
    match (c1, c2) {
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

pub fn of_neg(c: Curvature) -> Curvature {
    match c {
        Curvature::Convex   => { return Curvature::Concave; }
        Curvature::Concave  => { return Curvature::Convex; }
        Curvature::Affine   => { return Curvature::Affine; }
        Curvature::Constant => { return Curvature::Constant; }
        _ => { return Curvature::Unknown; }
    }
}

pub fn of_concave_fn(c: Curvature) -> Curvature {
    match c {
        Curvature::Concave  => { return Curvature::Concave; }
        Curvature::Affine   => { return Curvature::Concave; }
        Curvature::Constant => { return Curvature::Constant; }
        _ => { return Curvature::Unknown; }
    }
}

pub fn of_convex_fn(c: Curvature) -> Curvature {
    match c {
        Curvature::Convex   => { return Curvature::Convex; }
        Curvature::Affine   => { return Curvature::Convex; }
        Curvature::Constant => { return Curvature::Constant; }
        _ => { return Curvature::Unknown; }
    }
}

pub fn of_add(c1: Curvature, c2: Curvature) -> Curvature {
    match (c1, c2) {
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

pub fn of_sub(c1: Curvature, c2: Curvature) -> Curvature {
    return of_add(c1, of_neg(c2));
}

pub fn of_mul_by_const(c: Curvature, k: f64) -> Curvature {
    if k < 0.0 {
        return of_neg(c);
    } else if k > 0.0 {
        return c;
    } else {
        return Curvature::Constant;
    }
}

pub fn of_pow_by_const(c: Curvature, k: f64, d_o: Option<Domain>) -> Curvature {
    match c {
        Curvature::Constant => { 
            return Curvature::Constant;
        }
        Curvature::Affine => {
            // Case x^0.
            if k == 0.0 {
                return Curvature::Constant;
            // Case x^1.
            } else if k == 1.0 {
                return Curvature::Affine;
            // Case x^p with p < 0.
            } else if k < 0.0 {
                if domain::option_is_pos(d_o) {
                    return Curvature::Convex;
                } else {
                    return Curvature::Unknown;
                }
            // Case x^p with 0 < p < 1.
            } else if 0.0 < k && k < 1.0 {
                if domain::option_is_nonneg(d_o) {
                    return Curvature::Concave;
                } else {
                    return Curvature::Unknown;
                }
            // Case x^p with p = 2, 4, 6, ....
            } else if k == (k as u32) as f64 && (k as u32) % 2 == 0 {
                return Curvature::Convex;
            } else {
                if domain::option_is_nonneg(d_o) {
                    return Curvature::Convex;
                } else {
                    return Curvature::Unknown;
                }
            }
        }
        _ => { return Curvature::Unknown; }
    }
} 
