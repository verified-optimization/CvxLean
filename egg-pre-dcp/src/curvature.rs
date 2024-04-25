use core::cmp::Ordering;
use std::fmt;
use serde::Serialize;

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

impl Serialize for Curvature {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
        serializer.serialize_str(&self.to_string())
    }
}

pub fn join(c1: Curvature, c2: Curvature) -> Curvature {
    if c1 <= c2 { c2 } else if c2 <= c1 { c1 } else { Unknown }
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

// Composition rule for nondecreasing (or increasing) concave functions.
pub fn of_concave_nondecreasing_fn(c: Curvature) -> Curvature {
    match c {
        Concave  => { return Concave;  }
        Affine   => { return Concave;  }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

// Composition rule for nonincreasing (or decreasing) concave functions.
#[allow(unused)]
pub fn of_concave_nonincreasing_fn(c: Curvature) -> Curvature {
    match c {
        Convex   => { return Concave;  }
        Affine   => { return Concave;  }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

// Composition rule for concave functions with unknown monotonocity.
pub fn of_concave_none_fn(c: Curvature) -> Curvature {
    match c {
        Affine   => { return Concave;  }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

// Composition rule for nondecreasing (or increasing) convex functions.
pub fn of_convex_nondecreasing_fn(c: Curvature) -> Curvature {
    match c {
        Convex   => { return Convex;   }
        Affine   => { return Convex;   }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

// Composition rule for nonincreasing (or decreasing) convex functions.
pub fn of_convex_nonincreasing_fn(c: Curvature) -> Curvature {
    match c {
        Concave  => { return Convex;   }
        Affine   => { return Convex;   }
        Constant => { return Constant; }
        _        => { return Unknown;  }
    }
}

// Composition rule for concave functions with unknown monotonocity.
#[allow(unused)]
pub fn of_convex_none_fn(c: Curvature) -> Curvature {
    match c {
        Affine   => { return Convex;  }
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

pub fn of_mul_by_const(c: Curvature, k: Domain) -> Curvature {
    if domain::is_neg(&k) {
        return of_neg(c);
    } else if domain::is_pos(&k) {
        return c;
    } else if domain::is_zero(&k) {
        return Constant;
    } else {
        return Unknown;
    }
}

// This is a simplified version of `of_mul_by_const_full` that aligns with 
// the existing power atoms.
pub fn of_pow_by_const(c: Curvature, k: Domain, d_o: Option<Domain>) -> Curvature {
    match c {
        Constant => { 
            return Constant;
        }
        Affine => {
            // Case x^0.
            if domain::is_zero(&k) {
                return Constant;
            // Case x^1.
            } else if domain::is_one(&k) {
                return Affine;
            // Case x^2.
            } else if k.subseteq(&Domain::make_singleton(2.0)) {
                return Convex;
            // Case x^(-1).
            } else if k.subseteq(&Domain::make_singleton(-1.0)) {
                if domain::option_is_pos(d_o.as_ref()) {
                    return Convex;
                } else {
                    return Unknown;
                }
            // Case x^(-2).
            } else if k.subseteq(&Domain::make_singleton(-2.0)) {
                if domain::option_is_pos(d_o.as_ref()) {
                    return Convex;
                } else {
                    return Unknown;
                }
            } else {
                return Unknown;
            }
        }
        _ => { return Unknown; }
    }
} 

#[allow(unused)]
pub fn of_pow_by_const_full(c: Curvature, k: Domain, d_o: Option<Domain>) -> Curvature {
    match c {
        Constant => { 
            return Constant;
        }
        Affine => {
            // Case x^0.
            if domain::is_zero(&k) {
                return Constant;
            // Case x^1.
            } else if domain::is_one(&k) {
                return Affine;
            // Case x^p with p < 0.
            } else if domain::is_neg(&k) {
                if domain::option_is_pos(d_o.as_ref()) {
                    return Convex;
                } else {
                    return Unknown;
                }
            // Case x^p with 0 < p < 1.
            } else if k.subseteq(&Domain::make_oo(domain::zero(), domain::one())) {
                if domain::option_is_nonneg(d_o.as_ref()) {
                    return Concave;
                } else {
                    return Unknown;
                }
            // Cases x^p with p > 1
            } else if k.subseteq(&Domain::make_oi(domain::one())) {
                let mut is_pow_even = false;
                match k.get_constant() {
                    Some(k_f) => {
                        if k_f == (k_f as u32) as f64 && (k_f as u32).is_power_of_two() {
                            is_pow_even = true;
                        } 
                    }
                    _ => {}
                }
                // Case x^p with p = 2, 4, 8, ...
                if is_pow_even {
                    return Convex;
                // Case x^p with p > 1 and p != 2, 4, 8, ...
                } else {
                    if domain::option_is_nonneg(d_o.as_ref()) {
                        return Convex;
                    } else {
                        return Unknown;
                    }
                }
            } else {
                return Unknown;
            }
        }
        _ => { return Unknown; }
    }
} 
