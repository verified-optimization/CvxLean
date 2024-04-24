use core::cmp::Ordering;
use serde::{Deserialize, Serialize, Deserializer, Serializer, ser::SerializeSeq};
use intervals_good::*;
use rug::{Float, float::Round, ops::DivAssignRound, ops::PowAssignRound};


/* Constants. */

const F64_PREC: u32 = 53;

pub fn make_float(f: f64) -> Float { Float::with_val(F64_PREC, f) }

pub fn zero() -> Float { make_float(0.0) }

pub fn neg_zero() -> Float { make_float(-0.0) }

pub fn one() -> Float { make_float(1.0) }

pub fn neg_one() -> Float { make_float(-1.0) }

pub fn inf() -> Float { make_float(f64::INFINITY) }

pub fn neg_inf() -> Float { make_float(f64::NEG_INFINITY) }

const NO_ERROR: ErrorInterval = ErrorInterval { lo: false, hi: false };


/* Domain. */

// Extension of intervals-good intervals keeping track of opennes at the 
// endpoints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Domain {
    interval: Interval,
    lo_open: bool,
    hi_open: bool,
}

impl Domain {
    /* Getters. */

    fn lo_float(&self) -> &Float {
        self.interval.lo.as_float()
    }
    
    fn hi_float(&self) -> &Float {
        self.interval.hi.as_float()
    }

    /* Constructors. */

    pub fn make(interval: Interval, lo_open: bool, hi_open: bool) -> Self {
        // Ensure that infinite endpoints are open.
        let lo_is_infinte = interval.lo.as_float().is_infinite().clone();
        let hi_is_infinte = interval.hi.as_float().is_infinite().clone();
        Domain {
            interval: interval,
            lo_open: lo_open || lo_is_infinte,
            hi_open: hi_open || hi_is_infinte
        }
    }

    pub fn make_from_endpoints(lo: Float, hi: Float, lo_open: bool, hi_open: bool) -> Self {
        let interval = Interval::make(lo, hi, NO_ERROR);
        Domain::make(interval, lo_open, hi_open)
    }

    pub fn make_singleton(f: f64) -> Domain {
        let f_f = make_float(f);
        Domain::make_from_endpoints(
            f_f.clone(), f_f.clone(), false, false
        )
    }

    pub fn make_cc(lo: Float, hi: Float) -> Self {
        Domain::make_from_endpoints(lo, hi, false, false)
    }

    pub fn make_co(lo: Float, hi: Float) -> Self {
        Domain::make_from_endpoints(lo, hi, false, true)
    }

    pub fn make_ci(lo: Float) -> Self {
        Domain::make_from_endpoints(lo, inf(), false, true)
    }

    pub fn make_oc(lo: Float, hi: Float) -> Self {
        Domain::make_from_endpoints(lo, hi, true, false)
    }

    pub fn make_oo(lo: Float, hi: Float) -> Self {
        Domain::make_from_endpoints(lo, hi, true, true)
    }

    pub fn make_oi(lo: Float) -> Self {
        Domain::make_from_endpoints(lo, inf(), true, true)
    }

    pub fn make_ic(hi: Float) -> Self {
        Domain::make_from_endpoints(neg_inf(), hi, true, false)
    }

    pub fn make_io(hi: Float) -> Self {
        Domain::make_from_endpoints(neg_inf(), hi, true, true)
    }

    pub fn make_ii() -> Self {
        Domain::make_from_endpoints(neg_inf(), inf(), true, true)
    }

    /* Comparisons. */

    pub fn subseteq(&self, other: &Domain) -> bool {
        let self_lo = self.lo_float();
        let self_hi = self.hi_float();
        let self_lo_open = self.lo_open;
        let self_hi_open = self.hi_open;

        let other_lo = other.lo_float();
        let other_hi = other.hi_float();
        let other_lo_open = other.lo_open;
        let other_hi_open = other.hi_open;

        let left_inclusion = 
            if !self_lo_open && other_lo_open { 
                // ( ... [ ...
                other_lo < self_lo
            } else {
                other_lo <= self_lo
            };
        
        let right_inclusion =
            if !self_hi_open && other_hi_open {
                // ... ] ... )
                self_hi < other_hi
            } else {
                self_hi <= other_hi
            };
        
        left_inclusion && right_inclusion
    }

    pub fn eq(&self, other: &Domain) -> bool {
        self.subseteq(other) && other.subseteq(self)
    }

    /* Union and intersection. */

    pub fn union(&self, other: &Domain) -> Domain {
        let self_lo = self.lo_float();
        let self_hi = self.hi_float();
        let other_lo = other.lo_float();
        let other_hi = other.hi_float();

        let (lo, lo_open) = 
            if self_lo < other_lo {
                (self_lo, self.lo_open)
            } else if other_lo < self_lo {
                (other_lo, other.lo_open)
            } else {
                (self_lo, self.lo_open && other.lo_open)
            };
        
        let (hi, hi_open) =
            if other_hi < self_hi {
                (self_hi, self.hi_open)
            } else if self_hi < other_hi {
                (other_hi, other.hi_open)
            } else {
                (self_hi, self.hi_open && other.hi_open)
            };
        
        Domain::make_from_endpoints(lo.clone(), hi.clone(), lo_open, hi_open)
    }

    pub fn intersection(&self, other: &Domain) -> Domain {
        let self_lo = self.lo_float();
        let self_hi = self.hi_float();
        let other_lo = other.lo_float();
        let other_hi = other.hi_float();
        
        let (lo, lo_open) = 
            if self_lo < other_lo {
                (other_lo, other.lo_open)
            } else if other_lo < self_lo {
                (self_lo, self.lo_open)
            } else {
                (self_lo, self.lo_open || other.lo_open)
            };

        let (hi, hi_open) =
            if other_hi < self_hi {
                (other_hi, other.hi_open)
            } else if self_hi < other_hi {
                (self_hi, self.hi_open)
            } else {
                (self_hi, self.hi_open || other.hi_open)
            };

        Domain::make_from_endpoints(lo.clone(), hi.clone(), lo_open, hi_open)
    }

    /* Is empty. */

    pub fn is_empty(&self) -> bool {
        let lo = self.lo_float();
        let hi = self.hi_float();
        if lo.is_nan() || hi.is_nan() {
            true 
        } else {
            match (lo.is_infinite(), hi.is_infinite()) {
                (true, true) => lo.is_sign_positive() || !hi.is_sign_positive(),
                (true, false) => lo.is_sign_positive(),
                (false, true) => !hi.is_sign_positive(),
                _ => lo > hi || (lo == hi && (self.lo_open || self.hi_open))
            }  
        } 
    }

    /* Get constant. */

    pub fn get_constant(&self) -> Option<f64> {
        // If is singleton.
        let lo_f = self.lo_float();
        let hi_f = self.hi_float();
        if lo_f.is_finite() && hi_f.is_finite() && !self.lo_open && !self.hi_open {
            let lo_f64 = lo_f.to_f64();
            let hi_f64 = hi_f.to_f64();
            if lo_f64 == hi_f64 {
                Some(lo_f64)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn option_get_constant(d_o: Option<Domain>) -> Option<f64> {
        d_o.as_ref().map_or(None, Domain::get_constant)
    }
}

#[macro_export]
macro_rules! CC {
    ($a:expr, $b:expr) => { Domain::make_cc(domain::make_float($a), domain::make_float($b)) };
}

#[macro_export]
macro_rules! CO {
    ($a:expr, $b:expr) => { Domain::make_co(domain::make_float($a), domain::make_float($b)) };
}

#[macro_export]
macro_rules! CI {
    ($a:expr) => { Domain::make_ci(domain::make_float($a)) };
}

#[macro_export]
macro_rules! OC {
    ($a:expr, $b:expr) => { Domain::make_oc(domain::make_float($a), domain::make_float($b)) };
}

#[macro_export]
macro_rules! OO {
    ($a:expr, $b:expr) => { Domain::make_oo(domain::make_float($a), domain::make_float($b)) };
}

#[macro_export]
macro_rules! OI {
    ($b:expr) => { Domain::make_oi(domain::make_float($b)) };
}

#[macro_export]
macro_rules! IC {
    ($b:expr) => { Domain::make_ic(domain::make_float($b)) };
}

#[macro_export]
macro_rules! IO {
    ($b:expr) => { Domain::make_io(domain::make_float($b)) };
}

impl PartialOrd for Domain {
    fn partial_cmp(&self, other: &Domain) -> Option<Ordering> {
        if self.eq(other) {
            Some(Ordering::Equal)
        }
        else if self.subseteq(other) {
            Some(Ordering::Greater)
        }
        else if other.subseteq(self) {
            Some(Ordering::Less)
        }
        else {
            None
        }
    }
}


/* Serialize and deserialize. */

fn custom_string_to_float(s: String) -> Option<Float> {
    match s.as_str() {
        "inf" => Some(inf()),
        "-inf" => Some(neg_inf()),
        _ => {
            match s.parse::<f64>() {
                Ok(f) => Some(make_float(f)),
                _ => None
            }
        }
    }
}

fn custom_string_to_bool(s: String) -> bool {
    match s.as_str() {
        "0" => false,
        _ => true
    }
}

impl<'de> Deserialize<'de> for Domain {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de> 
    {
        let v: Vec<String> = Vec::deserialize(deserializer)?;
        if v.len() == 4 {
            // For example, [a, b) is represented by [a, b, 0, 1].
            let v0_f_o = custom_string_to_float(v[0].clone());
            let v1_f_o = custom_string_to_float(v[1].clone());
            let lo_open = custom_string_to_bool(v[2].clone());
            let hi_open = custom_string_to_bool(v[3].clone());
            match (v0_f_o, v1_f_o) {
                (Some(v0_f), Some(v1_f)) => {
                    let lo = Float::with_val(F64_PREC, v0_f);
                    let hi = Float::with_val(F64_PREC, v1_f);
                    Ok(Domain::make(
                        Interval::make(lo, hi, NO_ERROR),
                        lo_open,
                        hi_open,
                    ))
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

pub fn zero_dom() -> Domain { 
    Domain::make_cc(zero(), zero()) 
}

pub fn is_zero(d: &Domain) -> bool {
    d.eq(&zero_dom())
}

pub fn option_is_zero(d: Option<&Domain>) -> bool {
    d.map_or(false, is_zero)
}

pub fn one_dom() -> Domain { 
    Domain::make_cc(one(), one()) 
}

pub fn is_one(d: &Domain) -> bool {
    d.eq(&one_dom())
}

pub fn option_is_one(d: Option<&Domain>) -> bool {
    d.map_or(false, is_one)
}

pub fn free_dom() -> Domain { 
    Domain::make_ii()
}

pub fn empty_dom() -> Domain { 
    Domain::make_oo(zero(), zero())
}

pub fn pos_dom() -> Domain { 
    Domain::make_oi(zero())
}

pub fn is_pos(d: &Domain) -> bool {
    d.subseteq(&pos_dom())
}

pub fn option_is_pos(d: Option<&Domain>) -> bool {
    d.map_or(false, is_pos)
}

pub fn nonneg_dom() -> Domain { 
    Domain::make_ci(zero())
}

pub fn is_nonneg(d: &Domain) -> bool {
    d.subseteq(&nonneg_dom())
}

pub fn option_is_nonneg(d: Option<&Domain>) -> bool {
    d.map_or(false, is_nonneg)
}

pub fn nonpos_dom() -> Domain { 
    Domain::make_ic(neg_zero())
}

pub fn is_nonpos(d: &Domain) -> bool {
    d.subseteq(&nonpos_dom())
}

pub fn option_is_nonpos(d: Option<&Domain>) -> bool {
    d.map_or(false, is_nonpos)
}

pub fn neg_dom() -> Domain { 
    Domain::make_io(neg_zero())
}

pub fn is_neg(d: &Domain) -> bool {
    d.subseteq(&neg_dom())
}

// This really means that it does not contain zero.
pub fn does_not_contain_zero(d: &Domain) -> bool {
    !zero_dom().subseteq(d)
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

fn execute_binary<F>(d1_o: Option<Domain>, d2_o: Option<Domain>, f: F) -> Option<Domain>
    where
        F: FnOnce(&Domain, &Domain) -> Domain,
{
    match (d1_o, d2_o) {
        (Some(d1), Some(d2)) => { 
            let res = f(&d1, &d2);
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

pub fn abs(d: &Domain) -> Domain {
    let a = d.lo_float().clone();
    let a_abs = a.clone().abs();
    let b = d.hi_float().clone();
    let b_abs = b.clone().abs();
    let l = d.lo_open;
    let r = d.hi_open;
    if a.is_sign_negative() {
        if b.is_sign_negative() {
            Domain::make_from_endpoints(-b, -a, r, l)
        } else {
            if a_abs < b_abs {
                Domain::make_from_endpoints(zero(), b_abs, false, r)
            } else if b_abs < a_abs {
                Domain::make_from_endpoints(zero(), a_abs, false, l)
            } else {
                Domain::make_from_endpoints(zero(), a_abs, false, l && r)
            }
        }
    } else {
        Domain::make_from_endpoints(a, b, l, r)
    }
}

pub fn option_abs(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, abs)
}

pub fn sqrt(d: &Domain) -> Domain {
    if is_nonneg(d) {
        Domain::make(d.interval.sqrt(), d.lo_open, d.hi_open)
    } else {
        free_dom()
    }
}

pub fn option_sqrt(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, sqrt)
}

pub fn log(d: &Domain) -> Domain {
    if is_nonneg(d) {
        Domain::make(d.interval.ln(), d.lo_open, d.hi_open)
    } else {
        free_dom()
    }
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

pub fn xexp(d: &Domain) -> Domain {
    mul(d, &exp(d))
}

pub fn option_xexp(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, xexp)
}

pub fn entr(d: &Domain) -> Domain {
    neg(&mul(d, &log(d)))
}

pub fn option_entr(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, entr)
}

pub fn min(d1: &Domain, d2: &Domain) -> Domain {
    let a1 = d1.lo_float();
    let b1 = d1.hi_float();
    let a2 = d2.lo_float();
    let b2 = d2.hi_float();
    let l1 = d1.lo_open;
    let r1 = d1.hi_open;
    let l2 = d2.lo_open;
    let r2 = d2.hi_open; 
    let lo = a1.clone().min(a2);
    let hi = b1.clone().min(b2);
    let lo_open = if a1 < a2 { l1 } else if a2 < a1 { l2 } else { l1 && l2 };
    let hi_open = if b1 < b2 { r1 } else if b2 < b1 { r2 } else { r1 || r2 };
    Domain::make_from_endpoints(lo, hi, lo_open, hi_open)
}

pub fn option_min(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, min)
}

pub fn max(d1: &Domain, d2: &Domain) -> Domain {
    let a1 = d1.lo_float();
    let b1 = d1.hi_float();
    let a2 = d2.lo_float();
    let b2 = d2.hi_float();
    let l1 = d1.lo_open;
    let r1 = d1.hi_open;
    let l2 = d2.lo_open;
    let r2 = d2.hi_open; 
    let lo = a1.clone().max(a2);
    let hi = b1.clone().max(b2);
    let lo_open = if a1 > a2 { l1 } else if a2 > a1 { l2 } else { l1 || l2 };
    let hi_open = if b1 > b2 { r1 } else if b2 > b1 { r2 } else { r1 && r2 };
    Domain::make_from_endpoints(lo, hi, lo_open, hi_open)
}

pub fn option_max(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, max)
}

pub fn add(d1: &Domain, d2: &Domain) -> Domain {
    let l1 = d1.lo_open;
    let r1 = d1.hi_open;
    let l2 = d2.lo_open;
    let r2 = d2.hi_open; 
    Domain::make(
        d1.interval.add(&d2.interval),
        l1 || l2,
        r1 || r2
    )
}

pub fn option_add(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, add)
}

pub fn sub(d1: &Domain, d2: &Domain) -> Domain {
    let l1 = d1.lo_open;
    let r1 = d1.hi_open;
    let l2 = d2.lo_open;
    let r2 = d2.hi_open; 
    Domain::make(
        d1.interval.sub(&d2.interval),
        l1 || r2,
        r1 || l2
    )
}

pub fn option_sub(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, sub)
}

// Copied from interval-goods, but making multiplication by zero always be zero,
// with the correct sign.
fn perform_mult(
        lo1: &Float, lo2: &Float, 
        hi1: &Float, hi2: &Float,
        lo1_open: bool, lo2_open: bool,
        hi1_open: bool, hi2_open: bool) -> Domain {
    let mut lo = lo1.clone();
    let mut lo_open = lo1_open || lo2_open;
    if lo1.is_zero() || lo2.is_zero() {
        let neg_sign = lo1.is_sign_negative() ^ lo2.is_sign_negative();
        lo = if neg_sign { neg_zero() } else { zero() };
        lo_open = if lo1.is_zero() { lo1_open } else { lo2_open }
    } else {
        lo.mul_add_round(lo2, &Float::with_val(lo1.prec(), 0.0), Round::Down);
    }
    let mut hi = hi1.clone();
    let mut hi_open = hi1_open || hi2_open;
    if hi1.is_zero() || hi2.is_zero() {
        let neg_sign = hi1.is_sign_negative() ^ hi2.is_sign_negative();
        hi = if neg_sign { neg_zero() } else { zero() };
        hi_open = if hi1.is_zero() { hi1_open } else { hi2_open }
    } else {
        hi.mul_add_round(&hi2, &Float::with_val(hi1.prec(), 0.0), Round::Up);
    }
    let ival = Interval::make(lo, hi, NO_ERROR);
    Domain::make(ival, lo_open, hi_open)
}

// For multiplication, opennes of endpoints depends on the values.
pub fn mul(d1: &Domain, d2: &Domain) -> Domain {
    let d1_pos = is_pos(d1);
    let d1_neg = is_neg(d1);
    let d1_mix = !d1_pos && !d1_neg;

    let d2_pos = is_pos(d2);
    let d2_neg = is_neg(d2);
    let d2_mix = !d2_pos && !d2_neg;

    let a1 = d1.lo_float();
    let b1 = d1.hi_float();
    let l1 = d1.lo_open;
    let r1 = d1.hi_open;

    let a2 = d2.lo_float();
    let b2 = d2.hi_float();
    let l2 = d2.lo_open;
    let r2 = d2.hi_open;    

    if d1_pos && d2_pos {
        perform_mult(
            a1, a2, b1, b2,
            l1, l2, r1, r2)
    } else if d1_pos && d2_neg {
        perform_mult(
            b1, a2, a1, b2,
            r1, l2, l1, r2)
    } else if d1_pos && d2_mix {
        perform_mult(
            b1, a2, b1, b2,
            r1, l2, r1, r2)
    } else if d1_neg && d2_mix {
        perform_mult(
            a1, b2, a1, a2,
            l1, r2, l1, l2)
    } else if d1_neg && d2_pos {
        perform_mult(
            a1, b2, b1, a2,
            l1, r2, r1, l2)
    } else if d1_neg && d2_neg {
        perform_mult(
            b1, b2, a1, a2,
            r1, r2, l1, l2)
    } else if d1_mix && d2_pos {
        perform_mult(
            a1, b2, b1, b2,
            l1, r2, r1, r2)
    } else if d1_mix && d2_neg {
        perform_mult(
            b1, a2, a1, a2,
            r1, l2, l1, l2)
    }
    else {
        // Both intervals are mixed. 
        let du = perform_mult(
            b1, a2, a1, a2,
            r1, l2, l1, l2);
        
        let dv = perform_mult(
            a1, b2, b1, b2,
            l1, r2, r1, r2);
        
        du.union(&dv)
    }

}

pub fn option_mul(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, mul)
}

// Copied from intervals-good. Again, zero divided by anything is zero, with the
// correct sign. Note that this function is never used on denominator intervals
// containing zero, so it's safe to assume that we are always dividing by a 
// non-zero quanitity, even though hi2 and lo2 might be zero if they come from
// an open endpoint.
fn perform_div(
    lo1: &Float, lo2: &Float, 
    hi1: &Float, hi2: &Float,
    lo1_open: bool, lo2_open: bool,
    hi1_open: bool, hi2_open: bool) -> Domain {
    let mut lo = lo1.clone();
    let mut lo_open = lo1_open || lo2_open;
    if lo1.is_zero() {
        let neg_sign = lo1.is_sign_negative() ^ lo2.is_sign_negative();
        lo = if neg_sign { neg_zero() } else { zero() };
        lo_open = lo1_open;
    } else {
        lo.div_assign_round(lo2, Round::Down);
    }
    let mut hi = hi1.clone();
    let mut hi_open = hi1_open || hi2_open;
    if hi1.is_zero() {
        let neg_sign = hi1.is_sign_negative() ^ hi2.is_sign_negative();
        hi = if neg_sign { neg_zero() } else { zero() };
        hi_open = hi1_open;
    } else {
        hi.div_assign_round(hi2, Round::Up);
    }
    let ival = Interval::make(lo, hi, NO_ERROR);
    Domain::make(ival, lo_open, hi_open)
}

// Similar idea to multiplication, except for the division by zero cases.
pub fn div(d1: &Domain, d2: &Domain) -> Domain {
    let d1_pos = is_pos(d1);
    let d1_neg = is_neg(d1);
    let d1_mix = !d1_pos && !d1_neg;

    let d2_pos = is_pos(d2);
    let d2_neg = is_neg(d2);

    let a1 = d1.lo_float();
    let b1 = d1.hi_float();
    let l1 = d1.lo_open;
    let r1 = d1.hi_open;

    let a2 = d2.lo_float();
    let b2 = d2.hi_float();
    let l2 = d2.lo_open;
    let r2 = d2.hi_open;    

    if d1_pos && d2_pos {
        perform_div(
            a1, b2, b1, a2,
            l1, r2, r1, l2)
    } else if d1_pos && d2_neg {
        perform_div(
            b1, b2, a1, a2,
            r1, r2, l1, l2)
    } else if d1_neg && d2_pos {
        perform_div(
            a1, a2, b1, b2,
            l1, l2, r1, r2)
    } else if d1_neg && d2_neg {
        perform_div(
            b1, a2, a1, b2,
            r1, l2, l1, r2)
    } else if d1_mix && d2_pos {
        perform_div(
            a1, a2, b1, a2,
            l1, l2, r1, l2)
    } else if d1_mix && d2_neg {
        perform_div(
            b1, b2, a1, b2,
            r1, r2, l1, r2)
    } else {
        // Division by mixed (potentially zero), so the result is (-inf, inf).
        free_dom()
    }
}

pub fn option_div(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, div)
}

pub fn inv(d: &Domain) -> Domain {
    div(&one_dom(), d)
}

pub fn option_inv(d_o: Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, inv)
}

// Same reasoning as in `perform_mul`.
fn perform_pow(
    lo1: &Float, lo2: &Float, 
    hi1: &Float, hi2: &Float,
    lo1_open: bool, lo2_open: bool,
    hi1_open: bool, hi2_open: bool) -> Domain {
    let mut lo = lo1.clone();
    let mut lo_open = lo1_open || lo2_open;
    if lo2.is_zero() {
        lo = one();
        lo_open = lo2_open;
    } else if (lo1.is_zero() && lo2.is_sign_positive()) || lo1.eq(&one()) {
        lo_open = lo1_open;
    } else {
        lo.pow_assign_round(lo2, Round::Down);
    }

    let mut hi = hi1.clone();
    let mut hi_open = hi1_open || hi2_open;
    if hi2.is_zero() {
        hi = one();
        hi_open = hi2_open;
    } else if (hi1.is_zero() && hi2.is_sign_positive()) || hi1.eq(&one()) {
        hi_open = hi1_open;
    } else {
        hi.pow_assign_round(hi2, Round::Up);
    }

    let ival = Interval::make(lo, hi, NO_ERROR);
    Domain::make(ival, lo_open, hi_open)
}

pub fn pow(d1: &Domain, d2: &Domain) -> Domain {
    let d1_nonneg = is_nonneg(d1);
    if !d1_nonneg {
        // We only define rules for nonnegative bases.
        // However, if the exponent is a constant, we consider some special 
        // cases: 0, 1, and even natural numbers.
        match d2.get_constant() {
            Some(f) => {
                if ((f as u32) as f64) == f {
                    let n = f as u32;
                    if n == 0 {
                        return Domain::make_singleton(1.0);
                    } else if n == 1 {
                        return d1.clone();
                    } else if n > 0 && n % 2 == 0 {
                        let d = abs(d1);
                        let lo = d.lo_float();
                        let hi = d.hi_float();
                        let c = &make_float(f);
                        let l = d.lo_open;
                        let r = d.hi_open;
                        let res = 
                            perform_pow(
                                lo, c, hi, c,
                                l, false, r, false);
                        return res;
                    } else {
                        return free_dom();
                    }
                } else {
                    return free_dom();
                }
            }
            _ => {
                return free_dom();
            }
        }
    }

    let d1_lrg = d1.subseteq(&Domain::make_oi(one()));
    let d1_sml = d1.subseteq(&Domain::make_oo(zero(), one()));
    let d1_unk = !d1_lrg && !d1_sml;

    let d2_pos = is_pos(d2);
    let d2_neg = is_neg(d2);
    let d2_mix = !d2_pos && !d2_neg;

    let a1 = d1.lo_float();
    let b1 = d1.hi_float();
    let l1 = d1.lo_open;
    let r1 = d1.hi_open;

    let a2 = d2.lo_float();
    let b2 = d2.hi_float();
    let l2 = d2.lo_open;
    let r2 = d2.hi_open; 
    
    if d1_lrg && d2_pos {
        perform_pow(
            a1, a2, b1, b2,
            l1, l2, r1, r2)
    } else if d1_lrg && d2_neg {
        perform_pow(
            b1, a2, a1, b2,
            r1, l2, l1, r2)
    } else if d1_lrg && d2_mix {
        perform_pow(
            b1, a2, b1, b2, 
            r1, l2, r1, r2)
    } else if d1_sml && d2_pos {
        perform_pow(
            a1, b2, b1, a2,
            l1, r2, r1, l2)
    } else if d1_sml && d2_neg {
        perform_pow(
            b1, b2, a1, a2,
            r1, r2, l1, l2)
    } else if d1_sml && d2_mix {
        perform_pow(
            a1, b2, a1, a2,
            l1, r2, l1, l2)
    } else if d1_unk && d2_pos {
        perform_pow(
            a1, b2, b1, b2, 
            l1, r2, r1, r2)
    } else if d1_unk && d2_neg {
        perform_pow(
            b1, a2, a1, a2,
            r1, l2, l1, l2)
    } else {
        let du = perform_pow(
            b1, a2, a1, a2,
            r1, l2, l1, l2);
        
        let dv = perform_pow(
            a1, b2, b1, b2,
            l1, r2, r1, r2);
        
        du.union(&dv)
    }
}

pub fn option_pow(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, pow)
}

pub fn quad_over_lin(d1: &Domain, d2: &Domain) -> Domain {
    div(&pow(d1, &Domain::make_singleton(2.0)), d2)
}

pub fn option_quad_over_lin(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, quad_over_lin)
}

pub fn geo_mean(d1: &Domain, d2: &Domain) -> Domain {
    sqrt(&mul(d1, d2))
}

pub fn option_geo_mean(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, geo_mean)
}

pub fn log_sum_exp(d1: &Domain, d2: &Domain) -> Domain {
    log(&add(&exp(d1), &exp(d2)))
}

pub fn option_log_sum_exp(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, log_sum_exp)
}

pub fn norm2(d1: &Domain, d2: &Domain) -> Domain {
    sqrt(&add(&pow(d1, &Domain::make_singleton(2.0)), &pow(d2, &Domain::make_singleton(2.0))))
}

pub fn option_norm2(d1_o: Option<Domain>, d2_o: Option<Domain>) -> Option<Domain> {
    execute_binary(d1_o, d2_o, norm2)
}
