use core::cmp::Ordering;
use serde::{Deserialize, Serialize, Deserializer, Serializer, ser::SerializeSeq};
use intervals_good::*;
use rug::Float;

const F64_PREC: u32 = 53;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Domain(Interval);


/* Comparing domains. */

// a \subseteq b
fn subseteq(a: &Interval, b: &Interval) -> bool {
    let a_lo: Float = a.lo.clone().into();
    let a_hi: Float = a.hi.clone().into();
    let b_lo: Float = b.lo.clone().into();
    let b_hi: Float = b.hi.clone().into();

    return b_lo <= a_lo && a_hi <= b_hi;
}

impl PartialOrd for Domain {
    fn partial_cmp(&self, other: &Domain) -> Option<Ordering> {
        if *self == *other {
            return Some(Ordering::Equal);
        }
        if subseteq(&self.0, &other.0) {
            return Some(Ordering::Greater);
        }
        if subseteq(&other.0, &self.0) {
            return Some(Ordering::Less);
        }
        return None;
    }
}


/* Useful constants. */

fn zero() -> Float { Float::with_val(F64_PREC, 0.0) }

fn eps() -> Float { Float::with_val(F64_PREC, f64::EPSILON) }

fn neg_eps() -> Float { Float::with_val(F64_PREC, -f64::EPSILON) }

fn inf() -> Float { Float::with_val(F64_PREC, f64::INFINITY) }

fn neg_inf() -> Float { Float::with_val(F64_PREC, f64::NEG_INFINITY) }

const NO_ERROR: ErrorInterval = ErrorInterval { lo: false, hi: false };


/* Make domain from single float. */

pub fn singleton(f: f64) -> Domain {
    let f_f = Float::with_val(F64_PREC, f);
    Domain(Interval::make(f_f.clone(), f_f.clone(), NO_ERROR))
}


/* Serialize and deserialize. */

fn custom_string_to_float(s: &str) -> Option<Float> {
    match s {
        "eps" => Some(eps()),
        "-eps" => Some(neg_eps()),
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

impl<'de> Deserialize<'de> for Domain {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de> 
    {
        let v: Vec<&str> = Vec::deserialize(deserializer)?;
        if v.len() == 2 {
            let v0_f_o = custom_string_to_float(v[0]);
            let v1_f_o = custom_string_to_float(v[1]);
            match (v0_f_o, v1_f_o) {
                (Some(v0_f), Some(v1_f)) => {
                    let lo = Float::with_val(F64_PREC, v0_f);
                    let hi = Float::with_val(F64_PREC, v1_f);
                    Ok(Domain(Interval::make(lo, hi, NO_ERROR)))
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
        let lo: Float = self.0.lo.clone().into();
        let hi: Float = self.0.hi.clone().into();

        let mut s = serializer.serialize_seq(Some(2))?;
        s.serialize_element(&lo.to_f64())?;
        s.serialize_element(&hi.to_f64())?;
        s.end()
    }
}


/* Domain checks. */

pub fn is_zero(d: Domain) -> bool {
    let zero = Interval::make(zero(), zero(), NO_ERROR);
    subseteq(&d.0, &zero)
}

fn pos_interval() -> Interval { Interval::make(eps(), inf(), NO_ERROR) }

pub fn pos_d() -> Domain { Domain(pos_interval()) }

pub fn is_pos(d: Domain) -> bool {
    subseteq(&d.0, &pos_interval())
}

pub fn option_is_pos(d:Option<Domain>) -> bool {
    d.map_or(false, is_pos)
}

fn neg_interval() -> Interval { Interval::make(neg_inf(), neg_eps(), NO_ERROR) }

pub fn neg_d() -> Domain { Domain(neg_interval()) }

pub fn is_neg(d: Domain) -> bool {
    subseteq(&d.0, &neg_interval())
}

fn nonneg_interval() -> Interval { Interval::make(zero(), inf(), NO_ERROR) }

pub fn nonneg_d() -> Domain { Domain(nonneg_interval()) }

pub fn is_nonneg(d: Domain) -> bool {
    subseteq(&d.0, &nonneg_interval())
}

pub fn option_is_nonneg(d: Option<Domain>) -> bool {
    d.map_or(false, is_nonneg)
}

fn nonpos_interval() -> Interval { Interval::make(neg_inf(), zero(), NO_ERROR) }

pub fn nonpos_d() -> Domain { Domain(nonneg_interval()) }

pub fn is_nonpos(d: Domain) -> bool {
    subseteq(&d.0, &nonpos_interval())
}

// This really means that it does not contain zero.
pub fn is_nonzero(d: Domain) -> bool {
    !(d.0.contains(&zero()))
}


/* Execute operations handling errors (conservatively). */

fn execute_unary<F>(d_o: Option<Domain>, f: F) -> Option<Domain>
    where 
        F : FnOnce(Domain) -> Domain,
{
    match d_o {
        Some(d) => {
            let res = f(d);
            let may_error = res.0.err.lo || res.0.err.hi;
            if may_error {
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
        F: FnOnce(Domain, Domain) -> Domain,
{
    match (d_a_o, d_b_o) {
        (Some(d_a), Some(d_b)) => { 
            let res = f(d_a, d_b);
            let may_error = res.0.err.lo || res.0.err.hi;
            if may_error {
                None 
            } else {
                Some(res)
            }
        }
        _ => { None }
    }
}


/* Operations. */

pub fn neg(d:Domain) -> Domain {
    Domain(d.0.neg())
}

pub fn option_neg(d_o:Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, neg)
}

pub fn sqrt(d:Domain) -> Domain {
    Domain(d.0.sqrt())
}

pub fn option_sqrt(d_o:Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, sqrt)
}

pub fn log(d:Domain) -> Domain {
    Domain(d.0.ln())
}

pub fn option_log(d_o:Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, log)
}

pub fn exp(d:Domain) -> Domain {
    Domain(d.0.exp())
}

pub fn option_exp(d_o:Option<Domain>) -> Option<Domain> {
    execute_unary(d_o, exp)
}

pub fn add(d_a:Domain, d_b:Domain) -> Domain {
    Domain(d_a.0.add(&d_b.0))
}

pub fn option_add(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, add)
}

pub fn sub(d_a:Domain, d_b:Domain) -> Domain {
    Domain(d_a.0.sub(&d_b.0))
}

pub fn option_sub(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, sub)
}

pub fn mul(d_a:Domain, d_b:Domain) -> Domain {
    Domain(d_a.0.mul(&d_b.0))
}

pub fn option_mul(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, mul)
}

pub fn div(d_a:Domain, d_b:Domain) -> Domain {
    Domain(d_a.0.div(&d_b.0))
}

pub fn option_div(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, div)
}

pub fn pow(d_a:Domain, d_b:Domain) -> Domain {
    Domain(d_a.0.pow(&d_b.0))
}

pub fn option_pow(d_o_a:Option<Domain>, d_o_b:Option<Domain>) -> Option<Domain> {
    execute_binary(d_o_a, d_o_b, pow)
}


