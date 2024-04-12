/*!
Tests for extended interval arithmetic.
!*/

mod test_domain {

use egg_pre_dcp;

use egg_pre_dcp::domain;
use domain::Domain as Domain; 



/* Some useful intervals for testing apart from pos, nonneg, nonpos, neg. */

// gt_one 

// ge_one 

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


// is_zero (TODO).


// is_one (TODO).


// is_pos (TODO).


// is_nonneg (TODO: more).

#[test]
fn is_nonneg_1() {
    // [1, 1] is non-negative
    assert!(domain::is_nonneg(&Domain::make_singleton(1.0)));
}

// is_nonpos (TODO).


// is_neg (TODO).


// does_not_contain_zero (TODO).


}
