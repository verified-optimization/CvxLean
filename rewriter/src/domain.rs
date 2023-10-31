use core::{cmp::Ordering, panic};
use std::ops::Bound;
use serde::{Deserialize, Serialize};
use intervals_general::{interval::*, bound_pair::*};

#[derive(Debug, Clone, PartialEq)]
pub struct Domain(Interval<f64>);

impl PartialOrd for Domain {
    fn partial_cmp(&self, other: &Domain) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        if self.0.contains(&other.0) {
            return Some(Ordering::Greater);
        }
        if other.0.contains(&self.0) {
            return Some(Ordering::Less)
        }
        return None
    }
}

pub fn is_free(d:Domain) -> bool {
    return d.0 == Interval::Unbounded;
}

// Is {0} the same as [0,0] ??
// #[test]
// fn ttt() {
//     let x = Interval::Singleton { at: 0.0 } == Interval::Closed { bound_pair: BoundPair::new(0.0, 0.0).unwrap() };
//     print!("{}", x);
// }

pub fn is_zero(d: Domain) -> bool {
    let zero = Interval::Singleton { at: 0.0 };
    return zero.contains(&d.0);
}

pub fn is_pos(d: Domain) -> bool {
    let pos = Interval::UnboundedOpenLeft { left: 0.0 };
    return pos.contains(&d.0);
}

pub fn option_is_pos(d:Option<Domain>) -> bool {
    return d.map_or(false, is_pos);
}

pub fn is_neg(d: Domain) -> bool {
    let neg = Interval::UnboundedOpenRight { right: 0.0 };
    return neg.contains(&d.0);
}

pub fn is_nonneg(d: Domain) -> bool {
    let nonneg = Interval::UnboundedClosedLeft { left: 0.0 };
    return nonneg.contains(&d.0);
}

pub fn option_is_nonneg(d: Option<Domain>) -> bool {
    return d.map_or(false, is_nonneg);
}

pub fn is_nonpos(d: Domain) -> bool {
    let nonpos = Interval::UnboundedClosedRight { right: 0.0 };
    return nonpos.contains(&d.0);
}

pub fn is_nonzero(d: Domain) -> bool {
    let zero = Interval::Singleton { at: 0.0 };
    return !(d.0.contains(&zero));
}

fn flip_bound_pair(bound_pair: BoundPair<f64>) -> BoundPair<f64> {
    let l = bound_pair.left();
    let r = bound_pair.right();
    return BoundPair::new(-r, -l).unwrap();
}

pub fn flip(d:Domain) -> Domain {
    Domain(
        match d.0 {
            Interval::Closed { bound_pair } => {
                Interval::Closed { bound_pair: flip_bound_pair(bound_pair) }
            },
            Interval::Open { bound_pair } => {
                Interval::Open { bound_pair: flip_bound_pair(bound_pair) }
            },
            Interval::LeftHalfOpen { bound_pair } => {
                Interval::RightHalfOpen { bound_pair: flip_bound_pair(bound_pair) }
            },
            Interval::RightHalfOpen { bound_pair } => {
                Interval::LeftHalfOpen { bound_pair: flip_bound_pair(bound_pair) }
            },
            Interval::UnboundedClosedLeft { left } => {
                Interval::UnboundedClosedRight { right: -left }
            },
            Interval::UnboundedClosedRight { right } => {
                Interval::UnboundedClosedLeft { left: -right }
            },
            Interval::UnboundedOpenLeft { left } => {
                Interval::UnboundedOpenRight { right: -left }
            },
            Interval::UnboundedOpenRight { right } => {
                Interval::UnboundedOpenLeft { left: -right }
            },
            Interval::Singleton { at } => {
                Interval::Singleton { at: -at }
            },
            Interval::Unbounded => {
                Interval::Unbounded
            },
            Interval::Empty => {
                Interval::Empty
            }
        }
    )
}

pub fn option_flip(d:Option<Domain>) -> Option<Domain> {
    return d.map(flip);
}

// Copied from interval_general.
enum IntervalBound<T> {
    None,
    Unbounded,
    Open(T),
    Closed(T),
}

// TODO: Define adition of IntervalBound.
// TODO: Define multiplication of IntervalBound.
// TODO: Define min and max of bound.

// Copied from interval_general.
fn left_bound(i: &Interval<f64>) -> IntervalBound<f64> {
    match i {
        | Interval::Empty => IntervalBound::None,
        | Interval::Singleton { at } => IntervalBound::Closed(*at),
        // The cases where left bound of self is open -inf.
        | Interval::Unbounded
        | Interval::UnboundedClosedRight { .. }
        | Interval::UnboundedOpenRight { .. } => IntervalBound::Unbounded,
        // The cases where left bound of self is Closed and Bounded.
        | Interval::Closed { ref bound_pair}
        | Interval::RightHalfOpen { ref bound_pair } => 
            IntervalBound::Closed(*bound_pair.left()),
        | Interval::UnboundedClosedLeft { ref left } => 
            IntervalBound::Closed(*left),
        // The cases where left bound of self is Open and Bounded.
        | Interval::Open { ref bound_pair }
        | Interval::LeftHalfOpen { ref bound_pair } => 
            IntervalBound::Open(*bound_pair.left()),
        | Interval::UnboundedOpenLeft { ref left } => 
            IntervalBound::Open(*left),
    }
}

// Copied from interval_general.
fn right_bound(i: &Interval<f64>) -> IntervalBound<f64> {
    match i {
        | Interval::Empty => IntervalBound::None,
        | Interval::Singleton { ref at } => IntervalBound::Closed(*at),
        // The cases where right bound of self is open +inf.
        | Interval::Unbounded
        | Interval::UnboundedClosedLeft { .. }
        | Interval::UnboundedOpenLeft { .. } => IntervalBound::Unbounded,
        // The cases where right bound of self is Closed and Bounded.
        | Interval::Closed { ref bound_pair }
        | Interval::LeftHalfOpen { ref bound_pair } => 
            IntervalBound::Closed(*bound_pair.right()),
        | Interval::UnboundedClosedRight { ref right } => 
            IntervalBound::Closed(*right),
        // The cases where right bound of self is Open and Bounded.
        | Interval::Open { bound_pair }
        | Interval::RightHalfOpen { bound_pair } => 
            IntervalBound::Open(*bound_pair.right()),
        | Interval::UnboundedOpenRight { ref right } => 
            IntervalBound::Open(*right),
    }
}

// Conservative union, e.g., {-1} U {1} = [-1, 1].
pub fn union(d_a:Domain, d_b:Domain) -> Domain {
    let l = 
        match d_a.0.left_partial_cmp(&d_b.0) {
            | Some(Ordering::Equal)
            | Some(Ordering::Less) => { left_bound(&d_a.0) },
            | Some(Ordering::Greater) => { left_bound(&d_b.0) },
            | None => { IntervalBound::None }
        };
    let r = 
        match d_a.0.right_partial_cmp(&d_b.0) {
            | Some(Ordering::Equal)
            | Some(Ordering::Greater) => { right_bound(&d_a.0) },
            | Some(Ordering::Less) => { right_bound(&d_b.0) },
            | None => { IntervalBound::None }
        };
    return Domain(Interval::Empty);
}

// TODO: Move.
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
