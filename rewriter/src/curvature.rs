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

use Curvature::*;

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
        if *self == Constant {
            return Some(Ordering::Less);
        } 
        // Non-constant > Constant.
        if *other == Constant {
            return Some(Ordering::Greater);
        }
        // Affine < Non-affine.
        if *self == Affine {
            return Some(Ordering::Less);
        }
        // Non-affine > Affine.
        if *other == Affine {
            return Some(Ordering::Greater);
        }
        // Convex < Unknown.
        if *self == Convex && *other == Unknown {
            return Some(Ordering::Less);
        }
        // Unknown > Convex.
        if *self == Unknown && *other == Convex {
            return Some(Ordering::Greater);
        }
        // Concave < Unknown.
        if *self == Concave && *other == Unknown {
            return Some(Ordering::Less);
        }
        // Unknown > Concave.
        if *self == Unknown && *other == Concave {
            return Some(Ordering::Greater);
        }

        return None;
    }
}

impl fmt::Display for Curvature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Unknown  => write!(f, "Unknown"),
            Convex   => write!(f, "Convex"),
            Concave  => write!(f, "Concave"),
            Affine   => write!(f, "Affine"),
            Constant => write!(f, "Constant"),
        }
    }
}

pub fn of_le(c1: Curvature, c2: Curvature) -> Curvature {
    match (c1, c2) {
        (Convex,   Concave ) => { return Convex;   }
        (Convex,   Affine  ) => { return Convex;   }
        (Convex,   Constant) => { return Convex;   }
        (Affine,   Concave ) => { return Convex;   }
        (Constant, Concave ) => { return Convex;   }
        (Affine,   Affine  ) => { return Affine;   }
        (Constant, Affine  ) => { return Affine;   }
        (Affine,   Constant) => { return Affine;   }
        (Constant, Constant) => { return Constant; }
        _                    => { return Unknown;  }
    } 
}

pub fn of_neg(c: Curvature) -> Curvature {
    match c {
        Convex   => { return Concave;  }
        Concave  => { return Convex;   }
        Affine   => { return Affine;   }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

pub fn of_concave_fn(c: Curvature) -> Curvature {
    match c {
        Concave  => { return Concave;  }
        Affine   => { return Concave;  }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

pub fn of_convex_fn(c: Curvature) -> Curvature {
    match c {
        Convex   => { return Convex;   }
        Affine   => { return Convex;   }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

pub fn of_add(c1: Curvature, c2: Curvature) -> Curvature {
    match (c1, c2) {
        (Convex,   Convex  ) => { return Convex; }
        (Convex,   Affine  ) => { return Convex; }
        (Convex,   Constant) => { return Convex; }
        (Affine,   Convex  ) => { return Convex; }
        (Constant, Convex  ) => { return Convex; }

        (Concave,  Concave ) => { return Concave; }
        (Concave,  Affine  ) => { return Concave; }
        (Concave,  Constant) => { return Concave; }
        (Affine,   Concave ) => { return Concave; }
        (Constant, Concave ) => { return Concave; }

        (Affine,   Affine  ) => { return Affine; }
        (Affine,   Constant) => { return Affine; }
        (Constant, Affine  ) => { return Affine; }

        (Constant, Constant) => { return Constant; }
        
        _                    => { return Unknown; }
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
        return Constant;
    }
}

pub fn of_pow_by_const(c: Curvature, k: f64, d_o: Option<Domain>) -> Curvature {
    match c {
        Constant => { 
            return Constant;
        }
        Affine => {
            // Case x^0.
            if k == 0.0 {
                return Constant;
            // Case x^1.
            } else if k == 1.0 {
                return Affine;
            // Case x^p with p < 0.
            } else if k < 0.0 {
                if domain::option_is_pos(d_o) {
                    return Convex;
                } else {
                    return Unknown;
                }
            // Case x^p with 0 < p < 1.
            } else if 0.0 < k && k < 1.0 {
                if domain::option_is_nonneg(d_o) {
                    return Concave;
                } else {
                    return Unknown;
                }
            // Case x^p with p = 2, 4, 6, ....
            } else if k == (k as u32) as f64 && (k as u32) % 2 == 0 {
                return Convex;
            } else {
                if domain::option_is_nonneg(d_o) {
                    return Convex;
                } else {
                    return Unknown;
                }
            }
        }
        _ => { return Unknown; }
    }
} 
