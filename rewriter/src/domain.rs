use core::cmp::Ordering;
use serde::{Deserialize, Serialize, Deserializer, Serializer, ser::SerializeSeq};
use intervals_good::*;
use rug::{Float, float::Round, ops::DivAssignRound, ops::PowAssignRound};

const F64_PREC: u32 = 53;

// Extension of intervals-good intervals keeping track of opennes at the 
// endpoints. Unbounded endpoints are closed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Domain{
    interval: Interval,
    lo_open: bool,
    hi_open: bool,
}

impl Domain {
    fn lo_float(&self) -> &Float {
        self.interval.lo.as_float()
    }
    
    fn hi_float(&self) -> &Float {
        self.interval.hi.as_float()
    }

    // Turn -0 into 0.
    // fn adjust_zeros(&mut self) -> () {
    //     let lo = self.interval.lo.as_float_mut();
    //     if lo.is_zero() && lo.is_sign_negative() {
    //         lo.assign(Float::with_val(F64_PREC, 0.0));
    //     }
    //     let hi = self.interval.hi.as_float_mut();
    //     if hi.is_zero() && hi.is_sign_negative() {
    //         hi.assign(Float::with_val(F64_PREC, 0.0));
    //     }
    // }

    pub fn make(interval: Interval, lo_open: bool, hi_open: bool) -> Self {
        // let mut d = Domain {
        //     interval: interval,
        //     lo_open: lo_open,
        //     hi_open: hi_open
        // };
        // d.adjust_zeros();
        // d
        // Domain { interval: interval, lo_open: lo_open, hi_open: hi_open }

        // Ensure that infinite endpoints are closed.
        let lo_is_infinte = interval.lo.as_float().is_infinite().clone();
        let hi_is_infinte = interval.hi.as_float().is_infinite().clone();
        Domain {
            interval: interval,
            lo_open: lo_open && !lo_is_infinte,
            hi_open: hi_open && !hi_is_infinte
        }
    }

    pub fn make_from_endpoints(lo: Float, hi: Float, lo_open: bool, hi_open: bool) -> Self {
        let interval = Interval::make(lo, hi, NO_ERROR);
        Domain::make(interval, lo_open, hi_open)
    }
}


/* Comparing domains. */

// Interval "a" is a subset of interval "b", taking into account openness.
fn subseteq(a: &Domain, b: &Domain) -> bool {
    let a_lo = a.lo_float();
    let a_hi = a.hi_float();
    let a_lo_open = a.lo_open;
    let a_hi_open = a.hi_open;

    let b_lo = b.lo_float();
    let b_hi = b.hi_float();
    let b_lo_open = b.lo_open;
    let b_hi_open = b.hi_open;

    let same_infinite = |x: &Float, y: &Float| {
        x.is_infinite() && y.is_infinite() && 
        (x.is_sign_positive() == y.is_sign_positive())
    };

    let left_inclusion = 
        if !a_lo_open && b_lo_open { 
            // ( ... [ ...
            // NOTE: In the infinite case, ignore openness.
            b_lo < a_lo || same_infinite(a_lo, b_lo)
        } else {
            b_lo <= a_lo
        };
    let right_inclusion = 
        if !a_hi_open && b_hi_open {
            // ... ] ... )
            a_hi < b_hi || same_infinite(a_hi, b_hi)
        } else {
            a_hi <= b_hi
        };
    
    left_inclusion && right_inclusion
}

pub fn eq(a: &Domain, b: &Domain) -> bool {
    subseteq(a, b) && subseteq(b, a)
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

/* Domain union and intersection. */

#[allow(unused)]
pub fn union(d_a: &Domain, d_b: &Domain) -> Domain {
    let lo_a = d_a.lo_float();
    let hi_a = d_a.hi_float();
    let lo_b = d_b.lo_float();
    let hi_b = d_b.hi_float();
    let (lo, lo_open) = 
        if lo_a < lo_b {
            (lo_a, d_a.lo_open)
        } else if lo_b < lo_a {
            (lo_b, d_b.lo_open)
        } else {
            (lo_a, d_a.lo_open && d_b.lo_open)
        };
    let (hi, hi_open) =
        if hi_b < hi_a {
            (hi_a, d_a.hi_open)
        } else if hi_a < hi_b {
            (hi_b, d_b.hi_open)
        } else {
            (hi_a, d_a.hi_open && d_b.hi_open)
        };
    Domain::make_from_endpoints(lo.clone(), hi.clone(), lo_open, hi_open)
}

pub fn intersection(d_a: &Domain, d_b: &Domain) -> Domain {
    let lo_a = d_a.lo_float();
    let hi_a = d_a.hi_float();
    let lo_b = d_b.lo_float();
    let hi_b = d_b.hi_float();
    let (lo, lo_open) = 
        if lo_a < lo_b {
            (lo_b, d_b.lo_open)
        } else if lo_b < lo_a {
            (lo_a, d_a.lo_open)
        } else {
            (lo_a, d_a.lo_open || d_b.lo_open)
        };
    let (hi, hi_open) =
        if hi_b < hi_a {
            (hi_b, d_b.hi_open)
        } else if hi_a < hi_b {
            (hi_a, d_a.hi_open)
        } else {
            (hi_a, d_a.hi_open || d_b.hi_open)
        };
    Domain::make_from_endpoints(lo.clone(), hi.clone(), lo_open, hi_open)
}


/* Useful constants. */

pub fn zero() -> Float { Float::with_val(F64_PREC, 0.0) }

pub fn neg_zero() -> Float { Float::with_val(F64_PREC, -0.0) }

pub fn one() -> Float { Float::with_val(F64_PREC, 1.0) }

#[allow(unused)]
pub fn neg_one() -> Float { Float::with_val(F64_PREC, -1.0) }

pub fn inf() -> Float { Float::with_val(F64_PREC, f64::INFINITY) }

pub fn neg_inf() -> Float { Float::with_val(F64_PREC, f64::NEG_INFINITY) }

const NO_ERROR: ErrorInterval = ErrorInterval { lo: false, hi: false };


/* Make domain from single float. */

pub fn singleton(f: f64) -> Domain {
    let f_f = Float::with_val(F64_PREC, f);
    Domain::make(
        Interval::make(f_f.clone(), f_f.clone(), NO_ERROR),
        false,
        false
    )
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
        let lo = self.lo_float();
        let hi = self.hi_float();
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

pub fn zero_dom() -> Domain { 
    Domain::make(zero_ival(), false, false) 
}

#[allow(unused)]
pub fn is_zero(d: &Domain) -> bool {
    subseteq(d, &zero_dom())
}

fn free_ival() -> Interval { Interval::make(neg_inf(), inf(), NO_ERROR) }

pub fn free_dom() -> Domain { 
    Domain::make(free_ival(), false, false)
}

fn nonneg_ival() -> Interval { Interval::make(zero(), inf(), NO_ERROR) }

pub fn nonneg_dom() -> Domain { 
    Domain::make(nonneg_ival(), false, false)
}

pub fn is_nonneg(d: &Domain) -> bool {
    subseteq(d, &nonneg_dom())
}

pub fn option_is_nonneg(d: Option<&Domain>) -> bool {
    d.map_or(false, is_nonneg)
}

fn nonpos_ival() -> Interval { Interval::make(neg_inf(), neg_zero(), NO_ERROR) }

#[allow(unused)]
pub fn nonpos_dom() -> Domain { 
    Domain::make(nonpos_ival(), false, false)
}

#[allow(unused)]
pub fn is_nonpos(d: &Domain) -> bool {
    subseteq(d, &nonpos_dom())
}

pub fn pos_dom() -> Domain { 
    Domain::make(nonneg_ival(), true, false)
}

pub fn is_pos(d: &Domain) -> bool {
    subseteq(d, &pos_dom())
}

pub fn option_is_pos(d: Option<&Domain>) -> bool {
    d.map_or(false, is_pos)
}

pub fn neg_dom() -> Domain { 
    Domain::make(nonpos_ival(), false, true)
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
            let res_lo_f = res.lo_float();
            let res_hi_f = res.hi_float();
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
            let res_lo_f = res.lo_float();
            let res_hi_f = res.hi_float();
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
    Domain::make(d.interval.neg(), d.hi_open, d.lo_open)
}

pub fn option_neg(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, neg)
}

pub fn sqrt(d: &Domain) -> Domain {
    Domain::make(d.interval.sqrt(), d.lo_open, d.hi_open)
}

pub fn option_sqrt(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, sqrt)
}

pub fn log(d: &Domain) -> Domain {
    Domain::make(d.interval.ln(), d.lo_open, d.hi_open)
}

pub fn option_log(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, log)
}

pub fn exp(d: &Domain) -> Domain {
    Domain::make(d.interval.exp(), d.lo_open, d.hi_open)
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
    Domain::make(
        d_a.interval.add(&d_b.interval),
        d_a.lo_open || d_b.lo_open,
        d_a.hi_open || d_b.hi_open
    )
}

pub fn option_add(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, add)
}

pub fn sub(d_a: &Domain, d_b: &Domain) -> Domain {
    Domain::make(
        d_a.interval.sub(&d_b.interval),
        d_a.lo_open || d_b.hi_open,
        d_a.hi_open || d_b.lo_open
    )
}

pub fn option_sub(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, sub)
}

// The idea is that open "beats" closed.
fn choose_opennes(o_a: bool, o_b: bool) -> bool {
    o_a || o_b
}

// Copied from interval-goods, but making multiplication by zero always be zero,
// with the correct sign.
fn perform_mult(lo1: &Float, lo2: &Float, hi1: &Float, hi2: &Float) -> Interval {
    let mut lo = lo1.clone();
    if lo1.is_zero() || lo2.is_zero() {
        let neg_sign = lo1.is_sign_negative() ^ lo2.is_sign_negative();
        lo = if neg_sign { neg_zero() } else { zero() };
    } else {
        lo.mul_add_round(lo2, &Float::with_val(lo1.prec(), 0.0), Round::Down);
    }
    let mut hi = hi1.clone();
    if hi1.is_zero() || hi2.is_zero() {
        let neg_sign = hi1.is_sign_negative() ^ hi2.is_sign_negative();
        hi = if neg_sign { neg_zero() } else { zero() };
    } else {
        hi.mul_add_round(&hi2, &Float::with_val(hi1.prec(), 0.0), Round::Up);
    }
    Interval::make(lo, hi, NO_ERROR)
}

// For multiplication, opennes of endpoints depends on the values.
// NOTE(RFM): For the case splitting part, c.f. with `classify`.
pub fn mul(d_a: &Domain, d_b: &Domain) -> Domain {
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
                perform_mult(d_a.lo_float(), d_b.lo_float(), d_a.hi_float(), d_b.hi_float()),
                choose_opennes(d_a.lo_open, d_b.lo_open), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_pos && d_b_neg {
            (
                perform_mult(d_a.hi_float(), d_b.lo_float(), d_a.lo_float(), d_b.hi_float()),
                choose_opennes(d_a.hi_open, d_b.lo_open) , 
                choose_opennes(d_a.lo_open, d_b.hi_open) 
            )
        } else if d_a_pos && d_b_mix {
            (
                perform_mult(d_a.hi_float(), d_b.lo_float(), d_a.hi_float(), d_b.hi_float()),
                choose_opennes(d_a.hi_open, d_b.lo_open), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_neg && d_b_mix {
            (
                perform_mult(d_a.lo_float(), d_b.hi_float(), d_a.lo_float(), d_b.lo_float()),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_a.lo_open)
            )
        } else if d_a_neg && d_b_pos {
            (
                perform_mult(d_a.lo_float(), d_b.hi_float(), d_a.hi_float(), d_b.lo_float()),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.hi_open, d_b.lo_open)
            )
        } else if d_a_neg && d_b_neg {
            (
                perform_mult(d_a.hi_float(), d_b.hi_float(), d_a.lo_float(), d_b.lo_float()),
                choose_opennes(d_a.hi_open, d_b.hi_open),
                choose_opennes(d_a.lo_open, d_b.lo_open)
            )
        } else if d_a_mix && d_b_pos {
            (
                perform_mult(d_a.lo_float(), d_b.hi_float(), d_a.hi_float(), d_b.hi_float()),
                choose_opennes(d_a.lo_open, d_b.hi_open),
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_mix && d_b_neg {
            (
                perform_mult(d_a.hi_float(), d_b.lo_float(), d_a.lo_float(), d_b.lo_float()),
                choose_opennes(d_a.hi_open, d_b.lo_open),
                choose_opennes(d_a.lo_open, d_b.lo_open)
            )
        }
        else {
            // Both intervals are mixed. Union of:
            // 1. perform_mult(d_a.hi_float(), d_b.lo_float(), d_a.lo_float(), d_b.lo_float())
            // 2. perform_mult(d_a.lo_float(), d_b.hi_float(), d_a.hi_float(), d_b.hi_float())
            let ival1 = perform_mult(
                d_a.hi_float(), d_b.lo_float(), 
                d_a.lo_float(), d_b.lo_float());
            let lo1_open = choose_opennes(d_a.hi_open, d_b.lo_open);
            let hi1_open = choose_opennes(d_a.lo_open, d_b.lo_open);
            
            let ival2 = perform_mult(
                d_a.lo_float(), d_b.hi_float(), 
                d_a.hi_float(), d_b.hi_float());
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

    Domain::make(interval, lo_open, hi_open)
}

pub fn option_mul(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, mul)
}

// Copied from intervals-good. Again, zero divided by anything is zero, with the
// correct sign. Note that this function is never used on denominator intervals
// containing zero, so it's safe to assume that we are always dividing by a 
// non-zero quanitity, even though hi2 and lo2 might be zero if they come from
// an open endpoint.
fn perform_div(lo1: &Float, lo2: &Float, hi1: &Float, hi2: &Float) -> Interval {
    let mut lo = lo1.clone();
    if lo1.is_zero() {
        let neg_sign = lo1.is_sign_negative() ^ lo2.is_sign_negative();
        lo = if neg_sign { neg_zero() } else { zero() };
    } else {
        lo.div_assign_round(lo2, Round::Down);
    }
    let mut hi = hi1.clone();
    if hi1.is_zero() {
        let neg_sign = hi1.is_sign_negative() ^ hi2.is_sign_negative();
        hi = if neg_sign { neg_zero() } else { zero() };
    } else {
        hi.div_assign_round(hi2, Round::Up);
    }
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
                perform_div(d_a.lo_float(), d_b.hi_float(), d_a.hi_float(), d_b.lo_float()),
                // Interval is left-open if it comes from /inf.
                d_a.lo_open || d_b.hi_float().is_infinite(),
                d_a.hi_open
            )
        } else if d_a_pos && d_b_neg {
            (
                perform_div(d_a.hi_float(), d_b.hi_float(), d_a.lo_float(), d_b.lo_float()),
                d_a.hi_open,
                // Interval is right-open if it comes from /-inf.
                d_a.lo_open || d_b.lo_float().is_infinite()
            )
        } else if d_a_neg && d_b_pos {
            (
                perform_div(d_a.lo_float(), d_b.lo_float(), d_a.hi_float(), d_b.hi_float()),
                d_a.lo_open,
                // Interval is right-open if it comes from /inf.
                d_a.hi_open || d_b.hi_float().is_infinite()
            )
        } else if d_a_neg && d_b_neg {
            (
                perform_div(d_a.hi_float(), d_b.lo_float(), d_a.lo_float(), d_b.hi_float()),
                // Interval is left-open if it comes from /-inf.
                d_a.hi_open || d_b.lo_float().is_infinite(),
                d_a.lo_open
            )
        } else if d_a_mix && d_b_pos {
            (
                perform_div(d_a.lo_float(), d_b.lo_float(), d_a.hi_float(), d_b.lo_float()),
                d_a.lo_open,
                d_a.hi_open
            )
        } else if d_a_mix && d_b_neg {
            (
                perform_div(d_a.hi_float(), d_b.hi_float(), d_a.lo_float(), d_b.hi_float()),
                d_a.hi_open,
                d_a.lo_open
            )
        } else {
            // Division by mixed (potentially zero), so the result is [-inf, inf].
            (free_ival(), false, false)
        };

    Domain::make(interval, lo_open, hi_open)
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

    let d_b_pos = is_pos(d_b);
    let d_b_neg = is_neg(d_b);
    let d_b_mix = !d_b_pos && !d_b_neg;

    // This matches the rules for multiplication (self=d_a, other=d_b).
    let (interval, lo_open, hi_open) = 
        if d_a_pos && d_b_pos {
            (
                perform_pow(d_a.lo_float(), d_b.lo_float(), d_a.hi_float(), d_b.hi_float()),
                choose_opennes(d_a.lo_open, d_b.lo_open), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else if d_a_pos && d_b_neg {
            (
                perform_pow(d_a.hi_float(), d_b.lo_float(), d_a.lo_float(), d_b.hi_float()),
                // Interval is left-open if it comes from ^-inf.
                choose_opennes(d_a.hi_open, d_b.lo_open) || d_b.lo_float().is_infinite(), 
                choose_opennes(d_a.lo_open, d_b.hi_open)
            )
        } else if d_a_pos && d_b_mix {
            (
                perform_pow(d_a.hi_float(), d_b.lo_float(), d_a.hi_float(), d_b.hi_float()),
                // Interval is left-open if it comes from ^-inf.
                choose_opennes(d_a.hi_open, d_b.lo_open) || d_b.lo_float().is_infinite(), 
                choose_opennes(d_a.hi_open, d_b.hi_open)
            )
        } else {
            // Negative and mixed cases are problematic, so we overapproximate
            // them with the free domain.
            // TODO: support nonneg.
            (free_ival(), false, false)
        };

    Domain::make(interval, lo_open, hi_open)
}

pub fn option_pow(d_o_a: Option<Domain>, d_o_b: Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, pow)
}
