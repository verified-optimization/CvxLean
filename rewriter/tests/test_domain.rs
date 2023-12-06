use egg_convexify;

use egg_convexify::domain;
use domain::Domain as Domain; 


/* Tests for +, *, -, and / on critical intervals: 
    * Positive (0, +inf),
    * Non-negative [0, +inf),
    * Non-positive (-inf, 0],
    * Negative (-inf, 0).
*/


// Addition (10 tests, commutative).

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
fn add_neg_neg() {
    // (-inf, 0) + (-inf, 0) = (-inf, 0)
    let result = domain::add(&domain::neg_dom(), &domain::neg_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}


// Multiplication (16 tests, commutative).

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
fn mul_neg_neg() {
    // (-inf, 0) * (-inf, 0) = (0, +inf)
    let result = domain::mul(&domain::neg_dom(), &domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}


// Subtraction (16 tests, not commutative).

#[test]
fn sub_pos_pos() {
    // (0, +inf) - (0, +inf) = (-inf, +inf)
    let result = domain::sub(&domain::pos_dom(), &domain::pos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

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


// Division (17 tests, not commutative).

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

// Powers (16 tests, not commutative).

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


/* Other tests. */

#[test]
fn one_div_pos() {
    // [1, 1] / (0, +inf) = (0, +inf)
    let result = domain::div(&Domain::make_singleton(1.0), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}


/* Logarithm tests. */

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
    let result = domain::log(&Domain::make_co(domain::one(), domain::inf()));
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


/* Exponential tests. */

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
