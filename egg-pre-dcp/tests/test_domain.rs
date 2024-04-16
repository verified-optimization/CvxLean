/*!
Tests for extended interval arithmetic.
!*/

mod test_domain {

use egg_pre_dcp;

use egg_pre_dcp::domain;
use domain::Domain as Domain; 



/* Some useful intervals for testing apart from pos, nonneg, nonpos, neg. */

fn gt_one() {
    Domain::make_oi(domain::one());
}

fn ge_one() {
    Domain::make_ci(domain::one());
}

fn gt_two_lt_three() {
    Domain::make_oo(domain::make_float(2.0), domain::make_float(3.0));
}

// TODO: more



/* Operations */


// Negation (TODO).


// Absolute value (TODO).




// Square root (TODO).


// Min (TODO).


// Max (TODO).


// Addition (16 tests).

#[test]
fn add_pos_pos() {
    // (0, +inf) + (0, +inf) = (0, +inf)
    let result = domain::add(&domain::pos_dom(), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_pos_nonneg() {
    // (0, +inf) + [0, +inf) = (0, +inf)
    let result = domain::add(&domain::pos_dom(), &domain::nonneg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_pos_nonpos() {
    // (0, +inf) + (-inf, 0] = (-inf, +inf) 
    let result = domain::add(&domain::pos_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_pos_neg() {
    // (0, +inf) + (-inf, 0) = (-inf, +inf)
    let result = domain::add(&domain::pos_dom(), &domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonneg_pos() {
    // [0, +inf) + (0, +inf) = (0, +inf)
    let result = domain::add(&domain::nonneg_dom(), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonneg_nonneg() {
    // [0, +inf) + [0, +inf) = [0, +inf)
    let result = domain::add(&domain::nonneg_dom(), &domain::nonneg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonneg_nonpos() {
    // [0, +inf) + (-inf, 0] = (-inf, +inf)
    let result = domain::add(&domain::nonneg_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonneg_neg() {
    // [0, +inf) + (-inf, 0) = (-inf, +inf)
    let result = domain::add(&domain::nonneg_dom(), &domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonpos_pos() {
    // (-inf, 0] + (0, +inf) = (-inf, +inf)
    let result = domain::add(&domain::nonpos_dom(), &domain::pos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonpos_nonneg() {
    // (-inf, 0] + [0, +inf) = (-inf, +inf)
    let result = domain::add(&domain::nonpos_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonpos_nonpos() {
    // (-inf, 0] + (-inf, 0] = (-inf, 0]
    let result = domain::add(&domain::nonpos_dom(), &domain::nonpos_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_nonpos_neg() {
    // (-inf, 0] + (-inf, 0) = (-inf, 0)
    let result = domain::add(&domain::nonpos_dom(), &domain::neg_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_neg_pos() {
    // (-inf, 0) + (0, +inf) = (-inf, +inf)
    let result = domain::add(&domain::neg_dom(), &domain::pos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_neg_nonneg() {
    // (-inf, 0) + [0, +inf) = (-inf, +inf)
    let result = domain::add(&domain::neg_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_neg_nonpos() {
    // (-inf, 0) + (-inf, 0] = (-inf, 0)
    let result = domain::add(&domain::neg_dom(), &domain::nonpos_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn add_neg_neg() {
    // (-inf, 0) + (-inf, 0) = (-inf, 0)
    let result = domain::add(&domain::neg_dom(), &domain::neg_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}


// Multiplication (16 tests).

#[test]
fn mul_pos_pos() {
    // (0, +inf) * (0, +inf) = (0, +inf)
    let result = domain::mul(&domain::pos_dom(), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}


#[test]
fn mul_pos_nonneg() {
    // (0, +inf) * [0, +inf) = [0, +inf)
    let result = domain::mul(&domain::pos_dom(), &domain::nonneg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_pos_nonpos() {
    // (0, +inf) * (-inf, 0] = (-inf, 0]
    let result = domain::mul(&domain::pos_dom(), &domain::nonpos_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_pos_neg() {
    // (0, +inf) * (-inf, 0) = (-inf, 0)
    let result = domain::mul(&domain::pos_dom(), &domain::neg_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonneg_pos() {
    // [0, +inf) * (0, +inf) = [0, +inf)
    let result = domain::mul(&domain::nonneg_dom(), &domain::pos_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonneg_nonneg() {
    // [0, +inf) * [0, +inf) = [0, +inf)
    let result = domain::mul(&domain::nonneg_dom(), &domain::nonneg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonneg_nonpos() {
    // [0, +inf) * (-inf, 0] = (-inf, 0]
    let result = domain::mul(&domain::nonneg_dom(), &domain::nonpos_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonneg_neg() {
    // [0, +inf) * (-inf, 0) = (-inf, 0]
    let result = domain::mul(&domain::nonneg_dom(), &domain::neg_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonpos_pos() {
    // (-inf, 0] * (0, +inf) = (-inf, 0]
    let result = domain::mul(&domain::nonpos_dom(), &domain::pos_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonnpos_nonneg() {
    // (-inf, 0] * [0, +inf) = (-inf, 0]
    let result = domain::mul(&domain::nonpos_dom(), &domain::nonneg_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonpos_nonpos() {
    // (-inf, 0] * (-inf, 0] = [0, +inf)
    let result = domain::mul(&domain::nonpos_dom(), &domain::nonpos_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_nonpos_neg() {
    // (-inf, 0] * (-inf, 0) = [0, +inf)
    let result = domain::mul(&domain::nonpos_dom(), &domain::neg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_neg_pos() {
    // (-inf, 0) * (0, +inf) = (-inf, 0)
    let result = domain::mul(&domain::neg_dom(), &domain::pos_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_neg_nonneg() {
    // (-inf, 0) * [0, +inf) = (-inf, 0]
    let result = domain::mul(&domain::neg_dom(), &domain::nonneg_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_neg_nonpos() {
    // (-inf, 0) * (-inf, 0] = [0, +inf)
    let result = domain::mul(&domain::neg_dom(), &domain::nonpos_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn mul_neg_neg() {
    // (-inf, 0) * (-inf, 0) = (0, +inf)
    let result = domain::mul(&domain::neg_dom(), &domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}


// Subtraction (16 tests).

#[test]
fn sub_pos_nonneg() {
    // (0, +inf) - [0, +inf) = (-inf, +inf)
    let result = domain::sub(&domain::pos_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_pos_nonpos() {
    // (0, +inf) - (-inf, 0] = (0, +inf)
    let result = domain::sub(&domain::pos_dom(), &domain::nonpos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_pos_neg() {
    // (0, +inf) - (-inf, 0) = (0, +inf)
    let result = domain::sub(&domain::pos_dom(), &domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonneg_pos() {
    // [0, +inf) - (0, +inf) = (-inf, +inf)
    let result = domain::sub(&domain::nonneg_dom(), &domain::pos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonneg_nonneg() {
    // [0, +inf) - [0, +inf) = (-inf, +inf)
    let result = domain::sub(&domain::nonneg_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonneg_nonpos() {
    // [0, +inf) - (-inf, 0] = [0, +inf)
    let result = domain::sub(&domain::nonneg_dom(), &domain::nonpos_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonneg_neg() {
    // [0, +inf) - (-inf, 0) = [0, +inf)
    let result = domain::sub(&domain::nonneg_dom(), &domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonpos_pos() {
    // (-inf, 0] - (0, +inf) = (-inf, 0)
    let result = domain::sub(&domain::nonpos_dom(), &domain::pos_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonpos_nonneg() {
    // (-inf, 0] - [0, +inf) = (-inf, 0]
    let result = domain::sub(&domain::nonpos_dom(), &domain::nonneg_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonpos_nonpos() {
    // (-inf, 0] - (-inf, 0] = (-inf, +inf)
    let result = domain::sub(&domain::nonpos_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_nonpos_neg() {
    // (-inf, 0] - (-inf, 0) = (-inf, +inf)
    let result = domain::sub(&domain::nonpos_dom(), &domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_neg_pos() {
    // (-inf, 0) - (0, +inf) = (-inf, 0)
    let result = domain::sub(&domain::neg_dom(), &domain::pos_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_neg_nonneg() {
    // (-inf, 0) - [0, +inf) = (-inf, 0)
    let result = domain::sub(&domain::neg_dom(), &domain::nonneg_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_neg_nonpos() {
    // (-inf, 0) - (-inf, 0] = (-inf, +inf)
    let result = domain::sub(&domain::neg_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sub_neg_neg() {
    // (-inf, 0) - (-inf, 0) = (-inf, +inf)
    let result = domain::sub(&domain::neg_dom(), &domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}


// Division (18 tests).

#[test]
fn div_pos_pos() {
    // (0, +inf) / (0, +inf) = (0, +inf)
    let result = domain::div(&domain::pos_dom(), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_pos_nonneg() {
    // (0, +inf) / [0, +inf) = (-inf, +inf)
    let result = domain::div(&domain::pos_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_pos_nonpos() {
    // (0, +inf) / (-inf, 0] = (-inf, +inf)
    let result = domain::div(&domain::pos_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_pos_neg() {
    // (0, +inf) / (-inf, 0) = (-inf, 0)
    let result = domain::div(&domain::pos_dom(), &domain::neg_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonneg_pos() {
    // [0, +inf) / (0, +inf) = [0, +inf)
    let result = domain::div(&domain::nonneg_dom(), &domain::pos_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonneg_nonneg() {
    // [0, +inf) / [0, +inf) = (-inf, +inf)
    let result = domain::div(&domain::nonneg_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonneg_nonpos() {
    // [0, +inf) / (-inf, 0] = (-inf, +inf)
    let result = domain::div(&domain::nonneg_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonneg_neg() {
    // [0, +inf) / (-inf, 0) = (-inf, 0]
    let result = domain::div(&domain::nonneg_dom(), &domain::neg_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonpos_pos() {
    // (-inf, 0] / (0, +inf) = (-inf, 0)
    let result = domain::div(&domain::nonpos_dom(), &domain::pos_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonpos_nonneg() {
    // (-inf, 0] / [0, +inf) = (-inf, +inf)
    let result = domain::div(&domain::nonpos_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonpos_nonpos() {
    // (-inf, 0] / (-inf, 0] = (-inf, +inf)
    let result = domain::div(&domain::nonpos_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_nonpos_neg() {
    // (-inf, 0] / (-inf, 0) = [0, +inf)
    let result = domain::div(&domain::nonpos_dom(), &domain::neg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_neg_pos() {
    // (-inf, 0) / (0, +inf) = (-inf, 0)
    let result = domain::div(&domain::neg_dom(), &domain::pos_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_neg_nonneg() {
    // (-inf, 0) / [0, +inf) = (-inf, +inf)
    let result = domain::div(&domain::neg_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_neg_nonpos() {
    // (-inf, 0) / (-inf, 0] = (-inf, +inf)
    let result = domain::div(&domain::neg_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_neg_neg() {
    // (-inf, 0) / (-inf, 0) = (0, +inf)
    let result = domain::div(&domain::neg_dom(), &domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_free_pos() {
    // (-inf, +inf) / (-inf, 0) = (-inf, +inf)
    let result = domain::div(&domain::free_dom(), &domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_one_pos() {
    // [1, 1] / (0, +inf) = (0, +inf)
    let result = domain::div(&Domain::make_singleton(1.0), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}


// Power (16 tests).

#[test]
fn pow_pos_pos() {
    // (0, +inf) ^ (0, +inf) = (0, +inf)
    let result = domain::pow(&domain::pos_dom(), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_pos_nonneg() {
    // (0, +inf) ^ [0, +inf) = (0, +inf)
    let result = domain::pow(&domain::pos_dom(), &domain::nonneg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_pos_nonpos() {
    // (0, +inf) ^ (-inf, 0] = (0, +inf)
    let result = domain::pow(&domain::pos_dom(), &domain::nonpos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_pos_neg() {
    // (0, +inf) ^ (-inf, 0) = (0, +inf)
    let result = domain::pow(&domain::pos_dom(), &domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonneg_pos() {
    // [0, +inf) ^ (0, +inf) = [0, +inf)
    let result = domain::pow(&domain::nonneg_dom(), &domain::pos_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonneg_nonneg() {
    // [0, +inf) ^ [0, +inf) = [0, +inf)
    let result = domain::pow(&domain::nonneg_dom(), &domain::nonneg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonneg_nonpos() {
    // [0, +inf) ^ (-inf, 0] = (0, +inf)
    let result = domain::pow(&domain::nonneg_dom(), &domain::nonpos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonneg_neg() {
    // [0, +inf) ^ (-inf, 0) = (0, +inf)
    let result = domain::pow(&domain::nonneg_dom(), &domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonpos_pos() {
    // (-inf, 0] ^ (0, +inf) = (-inf, +inf)
    let result = domain::pow(&domain::nonpos_dom(), &domain::pos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonpos_nonneg() {
    // (-inf, 0] ^ [0, +inf) = (-inf, +inf)
    let result = domain::pow(&domain::nonpos_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonpos_nonpos() {
    // (-inf, 0] ^ (-inf, 0] = (-inf, +inf)
    let result = domain::pow(&domain::nonpos_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_nonpos_neg() {
    // (-inf, 0] ^ (-inf, 0) = (-inf, +inf)
    let result = domain::pow(&domain::nonpos_dom(), &domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_neg_pos() {
    // (-inf, 0) ^ (0, +inf) = (-inf, +inf)
    let result = domain::pow(&domain::neg_dom(), &domain::pos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_neg_nonneg() {
    // (-inf, 0) ^ [0, +inf) = (-inf, +inf)
    let result = domain::pow(&domain::neg_dom(), &domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_neg_nonpos() {
    // (-inf, 0) ^ (-inf, 0] = (-inf, +inf)
    let result = domain::pow(&domain::neg_dom(), &domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_neg_neg() {
    // (-inf, 0) ^ (-inf, 0) = (-inf, +inf)
    let result = domain::pow(&domain::neg_dom(), &domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}


// Logarithm (6 tests).

#[test]
fn log_pos() {
    // log((0, +inf)) = (-inf, +inf)
    let result = domain::log(&domain::pos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_nonneg() {
    // log([0, +inf)) = (-inf, +inf)
    let result = domain::log(&domain::nonneg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_ge_one() {
    // log([1, +inf)) = [0, +inf)
    let result = domain::log(&Domain::make_ci(domain::one()));
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_gt_one() {
    // log((1, +inf)) = (0, +inf)
    let result = domain::log(&Domain::make_oi(domain::one()));
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_le_one() {
    // log([0, 1]) = (-inf, 0]
    let result = domain::log(&Domain::make_cc(domain::zero(), domain::one()));
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_lt_one() {
    // log([0, 1)) = (-inf, 0)
    let result = domain::log(&Domain::make_co(domain::zero(), domain::one()));
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}


// Exponential (6 tests).

#[test]
fn exp_free() {
    // exp((-inf, +inf)) = (0, +inf)
    let result = domain::exp(&domain::free_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn exp_pos() {
    // exp((0, +inf)) = (1, +inf)
    let result = domain::exp(&domain::pos_dom());
    let expected = Domain::make_oi(domain::one());
    assert!(result.eq(&expected));
}

#[test]
fn exp_nonneg() {
    // exp([0, +inf)) = [1, +inf)
    let result = domain::exp(&domain::nonneg_dom());
    let expected = Domain::make_ci(domain::one());
    assert!(result.eq(&expected));
}

#[test]
fn exp_nonpos() {
    // exp((-inf, 0]) = (0, 1]
    let result = domain::exp(&domain::nonpos_dom());
    let expected = Domain::make_oc(domain::zero(), domain::one());
    assert!(result.eq(&expected));
}

#[test]
fn exp_neg() {
    // exp((-inf, 0)) = (0, 1)
    let result = domain::exp(&domain::neg_dom());
    let expected = Domain::make_oo(domain::zero(), domain::one());
    assert!(result.eq(&expected));
}



/* Checkers */


// Is zero?

#[test]
fn is_zero_zero() {
    // [0, 0] is zero
    assert!(domain::is_zero(&Domain::make_singleton(0.0)));
}

#[test]
fn not_is_zero_one() {
    // [1, 1] is not zero
    assert!(!domain::is_zero(&Domain::make_singleton(1.0)));
}

#[test]
fn not_is_zero_free() {
    // (-inf, +inf) is not zero
    assert!(!domain::is_zero(&domain::free_dom()));
}

#[test]
fn not_is_zero_empty() {
    // Empty set is not zero
    assert!(!domain::is_zero(&domain::empty_dom()));
}


// Is one?

#[test]
fn is_one_one() {
    // [1, 1] is one
    assert!(domain::is_one(&Domain::make_singleton(1.0)));
}

#[test]
fn not_is_one_zero() {
    // [0, 0] is not one
    assert!(!domain::is_one(&Domain::make_singleton(0.0)));
}

#[test]
fn not_is_one_free() {
    // (-inf, +inf) is not one
    assert!(!domain::is_one(&domain::free_dom()));
}

#[test]
fn not_is_one_empty() {
    // Empty set is not one
    assert!(!domain::is_one(&domain::empty_dom()));
}


// Is positive?

#[test]
fn is_pos_pos() {
    // (0, +inf) is positive
    assert!(domain::is_pos(&domain::pos_dom()));
}

#[test]
fn is_pos_one() {
    // [1, 1] is positive
    assert!(domain::is_pos(&Domain::make_singleton(1.0)));
}

#[test]
fn is_pos_empty() {
    // Empty set is positive
    assert!(domain::is_pos(&domain::empty_dom()));
}

#[test]
fn not_is_pos_nonneg() {
    // [0, +inf) is not positive
    assert!(!domain::is_pos(&domain::nonneg_dom()));
}

#[test]
fn not_is_pos_free() {
    // (-inf, +inf) is not positive
    assert!(!domain::is_pos(&domain::free_dom()));
}

#[test]
fn not_is_pos_zero() {
    // [0, 0] is not positive
    assert!(!domain::is_pos(&Domain::make_singleton(0.0)));
}


// Is non-negative?

#[test]
fn is_nonneg_pos() {
    // (0, +inf) is non-negative
    assert!(domain::is_nonneg(&domain::pos_dom()));
}

#[test]
fn is_nonneg_nonneg() {
    // [0, +inf) is non-negative
    assert!(domain::is_nonneg(&domain::nonneg_dom()));
}

#[test]
fn is_nonneg_zero() {
    // [0, 0] is non-negative
    assert!(domain::is_nonneg(&Domain::make_singleton(0.0)));
}

#[test]
fn is_nonneg_one() {
    // [1, 1] is non-negative
    assert!(domain::is_nonneg(&Domain::make_singleton(1.0)));
}

#[test]
fn is_nonneg_empty() {
    // Empty set is non-negative
    assert!(domain::is_nonneg(&domain::empty_dom()));
}

#[test]
fn not_is_nonneg_free() {
    // (-inf, +inf) is not non-negative
    assert!(!domain::is_nonneg(&domain::free_dom()));
}

#[test]
fn not_is_nonneg_minus_one() {
    // [-1, -1] is not non-negative
    assert!(!domain::is_nonneg(&Domain::make_singleton(-1.0)));
}


// Is non-positive?

#[test]
fn is_nonpos_nonpos() {
    // (-inf, 0] is non-positive
    assert!(domain::is_nonpos(&domain::nonpos_dom()));
}

#[test]
fn is_nonpos_neg() {
    // (-inf, 0) is non-positive
    assert!(domain::is_nonpos(&domain::neg_dom()));
}

#[test]
fn is_nonpos_zero() {
    // [0, 0] is non-positive
    assert!(domain::is_nonpos(&Domain::make_singleton(0.0)));
}

#[test]
fn is_nonpos_minus_one() {
    // [-1, -1] is non-positive
    assert!(domain::is_nonpos(&Domain::make_singleton(-1.0)));
}

#[test]
fn is_nonpos_empty() {
    // Empty set is non-positive
    assert!(domain::is_nonpos(&domain::empty_dom()));
}

#[test]
fn not_is_nonpos_free() {
    // (-inf, +inf) is not non-positive
    assert!(!domain::is_nonpos(&domain::free_dom()));
}

#[test]
fn not_is_nonpos_one() {
    // [1, 1] is not non-positive
    assert!(!domain::is_nonpos(&Domain::make_singleton(1.0)));
}


// Is negative?

#[test]
fn is_neg_neg() {
    // (-inf, 0) is negative
    assert!(domain::is_neg(&domain::neg_dom()));
}

#[test]
fn is_neg_minus_one() {
    // [-1, -1] is negative
    assert!(domain::is_neg(&Domain::make_singleton(-1.0)));
}

#[test]
fn is_neg_empty() {
    // Empty set is negative
    assert!(domain::is_neg(&domain::empty_dom()));
}

#[test]
fn not_is_neg_nonpos() {
    // (-inf, 0] is not negative
    assert!(!domain::is_neg(&domain::nonpos_dom()));
}

#[test]
fn not_is_neg_free() {
    // (-inf, +inf) is not negative
    assert!(!domain::is_neg(&domain::free_dom()));
}

#[test]
fn not_is_neg_zero() {
    // [0, 0] is not negative
    assert!(!domain::is_neg(&Domain::make_singleton(0.0)));
}

#[test]
fn not_is_neg_one() {
    // [1, 1] is not negative
    assert!(!domain::is_neg(&Domain::make_singleton(1.0)));
}


// Does not contain zero?

#[test]
fn does_not_contain_zero_pos() {
    // (0, +inf) does not contain zero
    assert!(domain::does_not_contain_zero(&domain::pos_dom()));
}

#[test]
fn does_not_contain_zero_neg() {
    // (-inf, 0) does not contain zero
    assert!(domain::does_not_contain_zero(&domain::neg_dom()));
}

#[test]
fn does_not_contain_zero_one() {
    // [1, 1] does not contain zero
    assert!(domain::does_not_contain_zero(&Domain::make_singleton(1.0)));
}

#[test]
fn does_not_contain_zero_minus_one() {
    // [-1, -1] does not contain zero
    assert!(domain::does_not_contain_zero(&Domain::make_singleton(-1.0)));
}

#[test]
fn does_not_contain_zero_empty() {
    // Empty set does not contain zero
    assert!(domain::does_not_contain_zero(&domain::empty_dom()));
}

#[test]
fn not_does_not_contain_zero_free() {
    // (-inf, +inf) contains zero
    assert!(!domain::does_not_contain_zero(&domain::free_dom()));
}

#[test]
fn not_does_not_contain_zero_nonneg() {
    // [0, +inf) contains zero
    assert!(!domain::does_not_contain_zero(&domain::nonneg_dom()));
}

#[test]
fn not_does_not_contain_zero_nonpos() {
    // (-inf, 0] contains zero
    assert!(!domain::does_not_contain_zero(&domain::nonpos_dom()));
}

#[test]
fn not_does_not_contain_zero_zero() {
    // [0, 0] contains zero
    assert!(!domain::does_not_contain_zero(&Domain::make_singleton(0.0)));
}

}
