use core::cmp::Ordering;
use serde::{Deserialize, Serialize, Deserializer, Serializer, ser::SerializeSeq};
use intervals_good::*;
use rug::{Float, float::Round, ops::DivAssignRound, ops::PowAssignRound};

const F64_PREC: u32 = 53;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Domain{
    interval: Interval,
    lo_open: bool,
    hi_open: bool,
}

fn lo_float(d: &Domain) -> &Float {
    d.interval.lo.as_float()
}

fn hi_float(d: &Domain) -> &Float {
    d.interval.hi.as_float()
} 


/* Comparing domains. */

// Closed interval "a" is a subset of closed interval "b".
#[allow(unused)]
fn subseteq_ival(a: &Interval, b: &Interval) -> bool {
    let a_lo: Float = a.lo.clone().into();
    let a_hi: Float = a.hi.clone().into();
    let b_lo: Float = b.lo.clone().into();
    let b_hi: Float = b.hi.clone().into();

    return b_lo <= a_lo && a_hi <= b_hi;
}

// Same but with potentially open sides.
fn subseteq(a: &Domain, b: &Domain) -> bool {
    let a_lo = lo_float(a);
    let a_hi = hi_float(a);
    let a_lo_open = a.lo_open;
    let a_hi_open = a.hi_open;

    let b_lo = lo_float(b);
    let b_hi = hi_float(b);
    let b_lo_open = b.lo_open;
    let b_hi_open = b.hi_open;

    let left_inclusion = 
        if !a_lo_open && b_lo_open { 
            // ( ... [ ...
            b_lo < a_lo
        } else {
            b_lo <= a_lo
        };
    let right_inclusion = 
        if !a_hi_open && b_hi_open {
            // ... ] ... )
            a_hi < b_hi
        } else {
            a_hi <= b_hi
        };
    
    left_inclusion && right_inclusion
}

impl PartialOrd for Domain {
    fn partial_cmp(&self, other: &Domain) -> Option<Ordering> {
        if *self == *other {
            Some(Ordering::Equal)
        }
        else if subseteq(&self, &other) {
            Some(Ordering::Greater)
        }
        else if subseteq(&other, &self) {
            Some(Ordering::Less)
        }
        else {
            None
        }
    }
}


/* Useful constants. */

fn zero() -> Float { Float::with_val(F64_PREC, 0.0) }

fn inf() -> Float { Float::with_val(F64_PREC, f64::INFINITY) }

fn neg_inf() -> Float { Float::with_val(F64_PREC, f64::NEG_INFINITY) }

const NO_ERROR: ErrorInterval = ErrorInterval { lo: false, hi: false };


/* Make domain from single float. */

pub fn singleton(f: f64) -> Domain {
    let f_f = Float::with_val(F64_PREC, f);
    Domain {
        interval: Interval::make(f_f.clone(), f_f.clone(), NO_ERROR),
        lo_open: false,
        hi_open: false
    }
}


/* Serialize and deserialize. */

fn custom_string_to_float(s: &str) -> Option<Float> {
    match s {
        "inf" => Some(inf()),
        "-inf" => Some(neg_inf()),
        _ => {
            match s.parse::<f64>() {
                Ok(f) => Some(Float::with_val(F64_PREC, f)),
                _ => None
            }
        }
    }
}

fn string_to_bool(s: &str) -> bool {
    match s {
        "0" => false,
        _ => true
    }
}

impl<'de> Deserialize<'de> for Domain {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de> 
    {
        let v: Vec<&str> = Vec::deserialize(deserializer)?;
        if v.len() == 4 {
            // For example, [a, b) is represented by [a, b, 0, 1].
            let v0_f_o = custom_string_to_float(v[0]);
            let v1_f_o = custom_string_to_float(v[1]);
            let lo_open = string_to_bool(v[2]);
            let hi_open = string_to_bool(v[3]);
            match (v0_f_o, v1_f_o) {
                (Some(v0_f), Some(v1_f)) => {
                    let lo = Float::with_val(F64_PREC, v0_f);
                    let hi = Float::with_val(F64_PREC, v1_f);
                    Ok(Domain {
                        interval: Interval::make(lo, hi, NO_ERROR),
                        lo_open: lo_open,
                        hi_open: hi_open,
                    })
                }
                _ => Err(serde::de::Error::custom("Domain deserialization error."))
            } 
        } else {
            Err(serde::de::Error::custom("Domain deserialization error."))
        }
    }
}

impl Serialize for Domain {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer 
    {
        let lo = lo_float(self);
        let hi = hi_float(self);
        let lo_open = if self.lo_open { "1" } else { "0" };
        let hi_open = if self.hi_open { "1" } else { "0" };

        let mut s = serializer.serialize_seq(Some(2))?;
        s.serialize_element(&lo.to_f64())?;
        s.serialize_element(&hi.to_f64())?;
        s.serialize_element(lo_open)?;
        s.serialize_element(hi_open)?;
        s.end()
    }
}


/* Domain checks. */

fn zero_ival() -> Interval { Interval::make(zero(), zero(), NO_ERROR) }

fn zero_dom() -> Domain { 
    Domain { interval: zero_ival(), lo_open: false, hi_open: false }    
}

#[allow(unused)]
pub fn is_zero(d: &Domain) -> bool {
    subseteq(d, &zero_dom())
}

fn nonneg_ival() -> Interval { Interval::make(zero(), inf(), NO_ERROR) }

pub fn nonneg_dom() -> Domain { 
    Domain { interval: nonneg_ival(), lo_open: false, hi_open: false }
}

pub fn is_nonneg(d: &Domain) -> bool {
    subseteq(d, &nonneg_dom())
}

pub fn option_is_nonneg(d: Option<&Domain>) -> bool {
    d.map_or(false, is_nonneg)
}

fn nonpos_ival() -> Interval { Interval::make(neg_inf(), zero(), NO_ERROR) }

#[allow(unused)]
pub fn nonpos_dom() -> Domain { 
    Domain { interval: nonpos_ival(), lo_open: false, hi_open: false }
}

#[allow(unused)]
pub fn is_nonpos(d: &Domain) -> bool {
    subseteq(d, &nonpos_dom())
}

pub fn pos_dom() -> Domain { 
    Domain { interval: nonneg_ival(), lo_open: true, hi_open: false }
}

pub fn is_pos(d: &Domain) -> bool {
    subseteq(d, &pos_dom())
}

pub fn option_is_pos(d: Option<&Domain>) -> bool {
    d.map_or(false, is_pos)
}

pub fn neg_dom() -> Domain { 
    Domain { interval: nonpos_ival(), lo_open: false, hi_open: true }
}

pub fn is_neg(d: &Domain) -> bool {
    subseteq(d, &neg_dom())
}

// This really means that it does not contain zero.
pub fn is_nonzero(d: &Domain) -> bool {
    subseteq(&zero_dom(), d)
}


/* Execute operations handling errors (conservatively). */

fn execute_unary<F>(d_o: Option<Domain>, f: F) -> Option<Domain>
    where 
        F : FnOnce(&Domain) -> Domain,
{
    match d_o {
        Some(d) => {
            let res = f(&d);
            let res_lo_f = lo_float(&res);
            let res_hi_f = hi_float(&res);
            if res_lo_f.is_nan() || res_hi_f.is_nan() {
                None
            } else {
                Some(res)
            }
        }
        _ => { None }
    }
}

fn execute_binary<F>(d_a_o: Option<Domain>, d_b_o: Option<Domain>, f: F) -> Option<Domain>
    where
        F: FnOnce(&Domain, &Domain) -> Domain,
{
    match (d_a_o, d_b_o) {
        (Some(d_a), Some(d_b)) => { 
            let res = f(&d_a, &d_b);
            let res_lo_f = lo_float(&res);
            let res_hi_f = hi_float(&res);
            if res_lo_f.is_nan() || res_hi_f.is_nan() {
                None 
            } else {
                Some(res)
            }
        }
        _ => { None }
    }
}


/* Operations. */

pub fn neg(d: &Domain) -> Domain {
    Domain {
        interval: d.interval.neg(),
        lo_open: d.hi_open,
        hi_open: d.lo_open
    }
}

pub fn option_neg(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, neg)
}

pub fn sqrt(d: &Domain) -> Domain {
    Domain {
        interval: d.interval.sqrt(),
        lo_open: d.lo_open,
        hi_open: d.hi_open
    }
}

pub fn option_sqrt(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, sqrt)
}

pub fn log(d: &Domain) -> Domain {
    Domain {
        interval: d.interval.ln(),
        lo_open: d.lo_open,
        hi_open: d.hi_open
    }
}

pub fn option_log(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, log)
}

pub fn exp(d: &Domain) -> Domain {
    Domain {
        interval: d.interval.exp(),
        lo_open: d.lo_open,
        hi_open: d.hi_open
    }
}

// Special case, exp is always positive even if we don't know the domain. More
// fine-grained domains are also possible.
pub fn option_exp(d_o: Option<Domain>) -> Option<Domain> {
    match execute_unary(d_o, exp) {
        None => Some(pos_dom()),
        d_o => d_o
    }
}

pub fn add(d_a: &Domain, d_b: &Domain) -> Domain {
    Domain {
        interval: d_a.interval.add(&d_b.interval),
        lo_open: d_a.lo_open || d_b.lo_open,
        hi_open: d_a.hi_open || d_b.hi_open
    }
}

pub fn option_add(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, add)
}

pub fn sub(d_a: &Domain, d_b: &Domain) -> Domain {
    Domain {
        interval: d_a.interval.sub(&d_b.interval),
        lo_open: d_a.lo_open || d_b.hi_open,
        hi_open: d_a.hi_open || d_b.lo_open
    }
}

pub fn option_sub(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, sub)
}

// The idea is that open "beats" closed.
fn choose_opennes(o_a: bool, o_b: bool) -> bool {
    o_a || o_b
}

// Copied from interval-goods, but making multiplication by zero always be zero.
fn perform_mult(lo1: &Float, lo2: &Float, hi1: &Float, hi2: &Float) -> Interval {
    let mut lo = lo1.clone();
    lo.mul_add_round(lo2, &Float::with_val(lo1.prec(), 0.0), Round::Down);
    if lo1.is_zero() || lo2.is_zero() {
        lo = zero();
    }
    let mut hi = hi1.clone();
    hi.mul_add_round(&hi2, &Float::with_val(hi1.prec(), 0.0), Round::Up);
    if hi1.is_zero() || hi2.is_zero() {
        hi = zero();
    }
    Interval::make(lo, hi, NO_ERROR)
}

// For multiplication, opennes of endpoints depends on the values.
// NOTE(RFM): For the case splitting part, c.f. with `classify`.
pub fn mul(d_a: &Domain, d_b: &Domain) -> Domain {
    let d_a_pos = is_pos(d_a);
    let d_a_neg = is_neg(d_a);
    let d_a_mix = !d_a_pos && !d_a_neg;
    println!("A = pos {}, neg {}, mix {}", d_a_pos, d_a_neg, d_a_mix);

    let d_b_pos = is_pos(d_b);
    let d_b_neg = is_neg(d_b);
    let d_b_mix = !d_b_pos && !d_b_neg;
    println!("B = pos {}, neg {}, mix {}", d_b_pos, d_b_neg, d_b_mix);

    // This matches the rules for multiplication (self=d_a, other=d_b).
    let (interval, lo_open, hi_open) = 
        if d_a_pos && d_b_pos {
            (
                perform_mult(lo_float(d_a), lo_float(d_b), hi_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.lo_open), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_pos && d_b_neg {
            (
                perform_mult(hi_float(d_a), lo_float(d_b), lo_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.lo_open), 
                choose_opennes(d_a.lo_open, d_b.hi_open)
            )
        } else if d_a_pos && d_b_mix {
            (
                perform_mult(hi_float(d_a), lo_float(d_b), hi_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.lo_open), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_neg && d_b_mix {
            (
                perform_mult(lo_float(d_a), hi_float(d_b), lo_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_a.lo_open)
            )
        } else if d_a_neg && d_b_pos {
            (
                perform_mult(lo_float(d_a), hi_float(d_b), hi_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.hi_open, d_b.lo_open)
            )
        } else if d_a_neg && d_b_neg {
            (
                perform_mult(hi_float(d_a), hi_float(d_b), lo_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_b.lo_open)
            )
        } else if d_a_mix && d_b_pos {
            (
                perform_mult(lo_float(d_a), hi_float(d_b), hi_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_mix && d_b_neg {
            (
                perform_mult(hi_float(d_a), lo_float(d_b), lo_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.lo_open),
                choose_opennes(d_a.lo_open, d_b.lo_open)
            )
        }
        else {
            // Both intervals are mixed. Union of:
            // 1. perform_mult(hi_float(d_a), lo_float(d_b), lo_float(d_a), lo_float(d_b))
            // 2. perform_mult(lo_float(d_a), hi_float(d_b), hi_float(d_a), hi_float(d_b))
            let ival1 = perform_mult(
                hi_float(d_a), lo_float(d_b), 
                lo_float(d_a), lo_float(d_b));
            let lo1_open = choose_opennes(d_a.hi_open, d_b.lo_open);
            let hi1_open = choose_opennes(d_a.lo_open, d_b.lo_open);
            
            let ival2 = perform_mult(
                lo_float(d_a), hi_float(d_b), 
                hi_float(d_a), hi_float(d_b));
            let lo2_open = choose_opennes(d_a.lo_open, d_b.hi_open);
            let hi2_open = choose_opennes(d_a.hi_open, d_b.hi_open);

            let lo_open = 
                if ival1.lo < ival2.lo {
                    lo1_open
                } else if ival2.lo < ival1.lo {
                    lo2_open
                } else {
                    // This is a union, so if they have the same value and and 
                    // one of the endpoints is closed, the result should be 
                    // closed.
                    lo1_open && lo2_open
                };
            
            let hi_open =
                if ival2.hi < ival1.hi {
                    hi1_open
                } else if ival1.hi < ival2.hi {
                    hi2_open
                } else {
                    hi1_open && hi2_open
                };

            (ival1.union(&ival2), lo_open, hi_open)
        };

    Domain {
        interval: interval,
        lo_open: lo_open,
        hi_open: hi_open
    }
}

pub fn option_mul(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, mul)
}

// Copied from intervals-good.
fn perform_div(lo1: &Float, lo2: &Float, hi1: &Float, hi2: &Float) -> Interval {
    let mut lo = lo1.clone();
    lo.div_assign_round(lo2, Round::Down);
    let mut hi = hi1.clone();
    hi.div_assign_round(hi2, Round::Up);
    Interval::make(lo, hi, NO_ERROR)
}

// Similar idea to multiplication, except for the division by zero cases.
pub fn div(d_a: &Domain, d_b: &Domain) -> Domain {
    let d_a_pos = is_pos(d_a);
    let d_a_neg = is_neg(d_a);
    let d_a_mix = !d_a_pos && !d_a_neg;

    let d_b_pos = is_pos(d_b);
    let d_b_neg = is_neg(d_b);

    let (interval, lo_open, hi_open) =
        if d_a_pos && d_b_pos {
            (
                perform_div(lo_float(d_a), hi_float(d_b), hi_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.hi_open, d_b.lo_open)
            )
        } else if d_a_pos && d_b_neg {
            (
                perform_div(hi_float(d_a), hi_float(d_b), lo_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_b.lo_open)
            )
        } else if d_a_neg && d_b_pos {
            (
                perform_div(lo_float(d_a), lo_float(d_b), hi_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.lo_open),
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_neg && d_b_neg {
            (
                perform_div(hi_float(d_a), lo_float(d_b), lo_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.lo_open),
                choose_opennes(d_a.lo_open, d_b.hi_open)
            )
        } else if d_a_mix && d_b_pos {
            (
                perform_div(lo_float(d_a), lo_float(d_b), hi_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.lo_open),
                choose_opennes(d_a.hi_open, d_b.lo_open)
            )
        } else if d_a_mix && d_b_neg {
            (
                perform_div(hi_float(d_a), hi_float(d_b), lo_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_b.hi_open)
            )
        } else {
            // Division by mixed (potentially zero), so the result is [-inf, inf].
            let free = Interval::make(neg_inf(), inf(), NO_ERROR);
            (free, false, false)
        };

    Domain {
        interval: interval,
        lo_open: lo_open,
        hi_open: hi_open
    }
}

pub fn option_div(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, div)
}

// Same reasoning as in `perform_pow`
fn perform_pow(lo1: &Float, lo2: &Float, hi1: &Float, hi2: &Float) -> Interval {
    let mut tmp_lo = lo1.clone();
    tmp_lo.pow_assign_round(lo2, Round::Down);
    let mut tmp_hi = hi1.clone();
    tmp_hi.pow_assign_round(hi2, Round::Up);
    Interval::make(tmp_lo, tmp_hi, NO_ERROR)
}

// The opennes computation is copied from multiplication replacing 
// `perform_mult` with `perform_pow`.
pub fn pow(d_a: &Domain, d_b: &Domain) -> Domain {
    let d_a_pos = is_pos(d_a);
    let d_a_neg = is_neg(d_a);
    let d_a_mix = !d_a_pos && !d_a_neg;

    let d_b_pos = is_pos(d_b);
    let d_b_neg = is_neg(d_b);
    let d_b_mix = !d_b_pos && !d_b_neg;

    // This matches the rules for multiplication (self=d_a, other=d_b).
    let (interval, lo_open, hi_open) = 
        if d_a_pos && d_b_pos {
            (
                perform_pow(lo_float(d_a), lo_float(d_b), hi_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.lo_open), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_pos && d_b_neg {
            (
                perform_pow(hi_float(d_a), lo_float(d_b), lo_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.lo_open), 
                choose_opennes(d_a.lo_open, d_b.hi_open)
            )
        } else if d_a_pos && d_b_mix {
            (
                perform_pow(hi_float(d_a), lo_float(d_b), hi_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.lo_open), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_neg && d_b_mix {
            (
                perform_pow(lo_float(d_a), hi_float(d_b), lo_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_a.lo_open)
            )
        } else if d_a_neg && d_b_pos {
            (
                perform_pow(lo_float(d_a), hi_float(d_b), hi_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.hi_open, d_b.lo_open)
            )
        } else if d_a_neg && d_b_neg {
            (
                perform_pow(hi_float(d_a), hi_float(d_b), lo_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_b.lo_open)
            )
        } else if d_a_mix && d_b_pos {
            (
                perform_pow(lo_float(d_a), hi_float(d_b), hi_float(d_a), hi_float(d_b)),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_mix && d_b_neg {
            (
                perform_pow(hi_float(d_a), lo_float(d_b), lo_float(d_a), lo_float(d_b)),
                choose_opennes(d_a.hi_open, d_b.lo_open),
                choose_opennes(d_a.lo_open, d_b.lo_open)
            )
        }
        else {
            // Both intervals are mixed. Union of:
            // 1. perform_pow(hi_float(d_a), lo_float(d_b), lo_float(d_a), lo_float(d_b))
            // 2. perform_pow(lo_float(d_a), hi_float(d_b), hi_float(d_a), hi_float(d_b))
            let ival1 = perform_pow(
                hi_float(&d_a), lo_float(&d_b), 
                lo_float(&d_a), lo_float(&d_b));
            let lo1_open = choose_opennes(d_a.hi_open, d_b.lo_open);
            let hi1_open = choose_opennes(d_a.lo_open, d_b.lo_open);
            
            let ival2 = perform_pow(
                lo_float(&d_a), hi_float(&d_b), 
                hi_float(&d_a), hi_float(&d_b));
            let lo2_open = choose_opennes(d_a.lo_open, d_b.hi_open);
            let hi2_open = choose_opennes(d_a.hi_open, d_b.hi_open);

            let lo_open = 
                if ival1.lo < ival2.lo {
                    lo1_open
                } else if ival2.lo < ival1.lo {
                    lo2_open
                } else {
                    lo1_open && lo2_open
                };
            
            let hi_open =
                if ival2.hi < ival1.hi {
                    hi1_open
                } else if ival1.hi < ival2.hi {
                    hi2_open
                } else {
                    hi1_open && hi2_open
                };

            (ival1.union(&ival2), lo_open, hi_open)
        };

    Domain {
        interval: interval,
        lo_open: lo_open,
        hi_open: hi_open
    }
}

pub fn option_pow(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, pow)
}
