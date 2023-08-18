use core::cmp::Ordering;
use serde::{Deserialize, Serialize};

#[derive(Debug, Copy, Clone, Serialize, Deserialize, PartialEq, Eq)]
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

pub fn is_free(d:Domain) -> bool {
    return d == Domain::Free;
}

pub fn is_zero(d:Domain) -> bool {
    return d == Domain::Zero;
}

pub fn is_pos(d:Domain) -> bool {
    return d == Domain::Pos || d == Domain::PosConst;
}

pub fn option_is_pos(d:Option<Domain>) -> bool {
    return d.map_or(false, is_pos);
}

pub fn is_neg(d:Domain) -> bool {
    return d == Domain::Neg || d == Domain::NegConst;
}

pub fn is_nonneg(d:Domain) -> bool {
    return d == Domain::NonNeg || d == Domain::Zero || is_pos(d);
}

pub fn option_is_nonneg(d:Option<Domain>) -> bool {
    return d.map_or(false, is_nonneg);
}

pub fn is_nonpos(d:Domain) -> bool {
    return d == Domain::NonPos || d == Domain::Zero || is_neg(d);
}

pub fn flip(d:Domain) -> Domain {
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

pub fn option_flip(d:Option<Domain>) -> Option<Domain> {
    return d.map(flip);
}

pub fn union(d_a:Domain, d_b:Domain) -> Domain {
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

pub fn add(d_a:Domain, d_b:Domain) -> Domain {
    match (d_a, d_b) {
        (Domain::Zero,   _             ) => { return d_b; }
        (_,              Domain::Zero  ) => { return d_a; }
        (Domain::NonNeg, Domain::Pos   ) => { return Domain::Pos; }
        (Domain::Pos,    Domain::NonNeg) => { return Domain::Pos; }
        (Domain::NonPos, Domain::Neg   ) => { return Domain::Neg; }
        (Domain::Neg,    Domain::NonPos) => { return Domain::Neg; }
        _ => { return union(d_a, d_b); }
    }
}

pub fn option_add(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    return option_map2(d_o_a, d_o_b, add);
}

pub fn mul(d_a:Domain, d_b:Domain) -> Domain {
    if is_zero(d_a) || is_zero(d_b) {
        return Domain::Zero;
    } else if is_free(d_a) || is_free(d_b) {
        return Domain::Free;
    } else if is_nonneg(d_a) && is_nonneg(d_b) {
        return add(d_a, d_b);
    } else if is_nonpos(d_a) && is_nonpos(d_b) {
        return add(d_a, d_b);
    } else {
        // Opposite sign case.
        if is_nonpos(d_a) {
            return flip(d_b);
        } else if is_nonpos(d_b) {
            return flip(d_a);
        } else {
            return Domain::Free;
        }
    }
}

pub fn option_mul(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    return option_map2(d_o_a, d_o_b, mul);
}
