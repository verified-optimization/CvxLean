/*!
Tests for extended interval arithmetic.
!*/

mod test_domain {

use egg_pre_dcp;

use egg_pre_dcp::domain;
use domain::Domain as Domain; 



/* Some useful intervals for testing apart from pos, nonneg, nonpos, neg, free. */

// [-9, 6)
fn ge_minus_nine_lt_six() -> Domain {
    Domain::make_co(domain::make_float(-9.0), domain::make_float(6.0))
}

// (-9, 6]
fn gt_minus_nine_le_six() -> Domain {
    Domain::make_oc(domain::make_float(-9.0), domain::make_float(6.0))
}

// [-6, 0]
fn ge_minus_six_le_zero() -> Domain {
    Domain::make_cc(domain::make_float(-6.0), domain::neg_zero())
}

// (-6, 0]
fn gt_minus_six_le_zero() -> Domain {
    Domain::make_oc(domain::make_float(-6.0), domain::zero())
}

// (-6, 6)
fn gt_minus_six_lt_six() -> Domain {
    Domain::make_oo(domain::make_float(-6.0), domain::make_float(6.0))
}

// (-6, 6]
fn gt_minus_six_le_six() -> Domain {
    Domain::make_oc(domain::make_float(-6.0), domain::make_float(6.0))
}

// (-6, 9)
fn gt_minus_six_lt_nine() -> Domain {
    Domain::make_oo(domain::make_float(-6.0), domain::make_float(9.0))
}

// [-4, 4)
fn ge_minus_four_lt_four() -> Domain {
    Domain::make_co(domain::make_float(-4.0), domain::make_float(4.0))
}

// (-4, 4]
fn gt_minus_four_le_four() -> Domain {
    Domain::make_oc(domain::make_float(-4.0), domain::make_float(4.0))
}

// [-3, -2)
fn ge_minus_three_lt_minus_two() -> Domain {
    Domain::make_co(domain::make_float(-3.0), domain::make_float(-2.0))
}

// (-3, -2)
fn gt_minus_three_lt_minus_two() -> Domain {
    Domain::make_oo(domain::make_float(-3.0), domain::make_float(-2.0))
}

// (-3, 0]
fn gt_minus_three_le_zero() -> Domain {
    Domain::make_oc(domain::make_float(-3.0), domain::zero())
}

// (-3, 2)
fn gt_minus_three_lt_two() -> Domain {
    Domain::make_oo(domain::make_float(-3.0), domain::make_float(2.0))
}

// (-3, 3)
fn gt_minus_three_lt_three() -> Domain {
    Domain::make_oo(domain::make_float(-3.0), domain::make_float(3.0))
}

// [-2, 0]
fn ge_minus_two_le_zero() -> Domain {
    Domain::make_cc(domain::make_float(-2.0), domain::zero())
}

// [-2, 3)
fn ge_minus_two_lt_three() -> Domain {
    Domain::make_co(domain::make_float(-2.0), domain::make_float(3.0))
}

// (-2, 2)
fn gt_minus_two_lt_two() -> Domain {
    Domain::make_oo(domain::make_float(-2.0), domain::make_float(2.0))
}

// (-2, 2]
fn gt_minus_two_le_two() -> Domain {
    Domain::make_oc(domain::make_float(-2.0), domain::make_float(2.0))
}

// (-2, 3)
fn gt_minus_two_lt_three() -> Domain {
    Domain::make_oo(domain::make_float(-2.0), domain::make_float(3.0))
}

// (-2, 3]
fn gt_minus_two_le_three() -> Domain {
    Domain::make_oc(domain::make_float(-2.0), domain::make_float(3.0))
}

// [0, 1)
fn ge_zero_lt_one() -> Domain {
    Domain::make_co(domain::zero(), domain::one())
}

// [0, 1]
fn ge_zero_le_one() -> Domain {
    Domain::make_cc(domain::zero(), domain::one())
}

// [0, 2)
fn ge_zero_lt_two() -> Domain {
    Domain::make_co(domain::zero(), domain::make_float(2.0))
}

// [0, 2]
fn ge_zero_le_two() -> Domain {
    Domain::make_cc(domain::zero(), domain::make_float(2.0))
}

// [0, 3)
fn ge_zero_lt_three() -> Domain {
    Domain::make_co(domain::zero(), domain::make_float(3.0))
}

// [0, 6)
fn ge_zero_lt_six() -> Domain {
    Domain::make_co(domain::zero(), domain::make_float(6.0))
}

// [0, 6]
fn ge_zero_le_six() -> Domain {
    Domain::make_cc(domain::zero(), domain::make_float(6.0))
}

// (1, +inf)
fn gt_one() -> Domain {
    Domain::make_oi(domain::one())
}

// [1, +inf)
fn ge_one() -> Domain {
    Domain::make_ci(domain::one())
}

// (2, 3)
fn gt_two_lt_three() -> Domain {
    Domain::make_oo(domain::make_float(2.0), domain::make_float(3.0))
}

// (4, 9)
fn gt_four_lt_nine() -> Domain {
    Domain::make_oo(domain::make_float(4.0), domain::make_float(9.0))
}



/* Operations */


// Negation (6 tests).

#[test]
fn neg_pos() {
    // -(0, +inf) = (-inf, 0)
    let result = domain::neg(&domain::pos_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn neg_nonneg() {
    // -[0, +inf) = (-inf, 0]
    let result = domain::neg(&domain::nonneg_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn neg_nonpos() {
    // -(-inf, 0] = [0, +inf)
    let result = domain::neg(&domain::nonpos_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn neg_neg() {
    // -(-inf, 0) = (0, +inf)
    let result = domain::neg(&domain::neg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn neg_free() {
    // -(-inf, +inf) = (-inf, +inf)
    let result = domain::neg(&domain::free_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn neg_gt_two_lt_three() {
    // -(2, 3) = (-3, -2)
    let result = domain::neg(&gt_two_lt_three());
    let expected = gt_minus_three_lt_minus_two();
    assert!(result.eq(&expected));
}


// Absolute value (TODO).

#[test]
fn abs_gt_two_lt_three() {
    // abs((2, 3)) = (2, 3)
    let result = domain::abs(&gt_two_lt_three());
    let expected = gt_two_lt_three();
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_three_lt_minus_two() {
    // abs((-3, -2)) = (2, 3)
    let result = domain::abs(&gt_minus_three_lt_minus_two());
    let expected = gt_two_lt_three();
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_two_lt_three() {
    // abs((-2, 3)) = [0, 3)
    let result = domain::abs(&gt_minus_two_lt_three());
    let expected = ge_zero_lt_three();
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_three_lt_two() {
    // abs((-3, 2)) = [0, 3)
    let result = domain::abs(&gt_minus_three_lt_two());
    let expected = ge_zero_lt_three();
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_two_le_two() {
    // abs((-2, 2]) = [0, 2]
    let result = domain::abs(&gt_minus_two_le_two());
    let expected = ge_zero_le_two();
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_two_lt_two() {
    // abs((-2, 2)) = [0, 2)
    let result = domain::abs(&gt_minus_two_lt_two());
    let expected = ge_zero_lt_two();
    assert!(result.eq(&expected));
}


// Square root (5 tests).

#[test]
fn sqrt_pos() {
    // sqrt((0, +inf)) = (0, +inf)
    let result = domain::sqrt(&domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sqrt_nonneg() {
    // sqrt([0, +inf)) = [0, +inf)
    let result = domain::sqrt(&domain::nonneg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sqrt_nonpos() {
    // sqrt((-inf, 0]) = (-inf, +inf)
    let result = domain::sqrt(&domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sqrt_neg() {
    // sqrt((-inf, 0)) = (-inf, +inf)
    let result = domain::sqrt(&domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn sqrt_gt_two_lt_three_subseteq() {
    // sqrt((2, 3)) \subseteq (1.41, 1.74)
    let result = domain::sqrt(&gt_two_lt_three());
    let enclosure = Domain::make_oo(domain::make_float(1.41), domain::make_float(1.74));
    assert!(result.subseteq(&enclosure));
}


// Logarithm (9 tests).

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
fn log_nonpos() {
    // log((-inf, 0]) = (-inf, +inf)
    let result = domain::log(&domain::nonpos_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_neg() {
    // log((-inf, 0)) = (-inf, +inf)
    let result = domain::log(&domain::neg_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_ge_one() {
    // log([1, +inf)) = [0, +inf)
    let result = domain::log(&ge_one());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_gt_one() {
    // log((1, +inf)) = (0, +inf)
    let result = domain::log(&gt_one());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_ge_zero_le_one() {
    // log([0, 1]) = (-inf, 0]
    let result = domain::log(&ge_zero_le_one());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_ge_zero_lt_one() {
    // log([0, 1)) = (-inf, 0)
    let result = domain::log(&ge_zero_lt_one());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_gt_two_lt_three_subseteq() {
    // log((2, 3)) \subseteq (0.69, 1.10)
    let result = domain::log(&gt_two_lt_three());
    let enclosure = Domain::make_oo(domain::make_float(0.69), domain::make_float(1.10));
    assert!(result.subseteq(&enclosure));
}


// Exponential (7 tests).

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

#[test]
fn exp_gt_two_lt_three_subseteq() {
    // exp((2, 3)) \subseteq (7.38, 20.09)
    let result = domain::exp(&gt_two_lt_three());
    let enclosure = Domain::make_oo(domain::make_float(7.38), domain::make_float(20.09));
    assert!(result.subseteq(&enclosure));
}


// Addition (17 tests).

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

#[test]
fn add_gt_minus_two_le_two_ge_zero_lt_one() {
    // (-2, 2] + [0, 1) = (-2, 3)
    let result = domain::add(&gt_minus_two_le_two(), &ge_zero_lt_one());
    let expected = gt_minus_two_lt_three();
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

#[test]
fn sub_gt_minus_two_lt_three_ge_zero_le_one() {
    // (-2, 3) - [0, 1] = (-3, 3)
    let result = domain::sub(&gt_minus_two_lt_three(), &ge_zero_le_one());
    let expected = gt_minus_three_lt_three();
    assert!(result.eq(&expected));
}


// Multiplication (30 tests).

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

#[test]
fn mul_gt_two_lt_three_gt_two_lt_three() {
    // (2, 3) * (2, 3) = (4, 9)
    let result = domain::mul(&gt_two_lt_three(), &gt_two_lt_three());
    let expected = gt_four_lt_nine();
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_gt_minus_three_lt_minus_two() {
    // [-3, -2) * (-3, -2) = (4, 9)
    let result = domain::mul(&ge_minus_three_lt_minus_two(), &gt_minus_three_lt_minus_two());
    let expected = gt_four_lt_nine();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_ge_zero_le_two() {
    // (2, 3) * [0, 2] = [0, 6)
    let result = domain::mul(&gt_two_lt_three(), &ge_zero_le_two());
    let expected = ge_zero_lt_six();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_ge_minus_two_le_zero() {
    // (2, 3) * [-2, 0] = (-6, 0]
    let result = domain::mul(&gt_two_lt_three(), &ge_minus_two_le_zero());
    let expected = gt_minus_six_le_zero();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_gt_minus_two_le_three() {
    // (2, 3) * (-2, 3] = (-6, 9)
    let result = domain::mul(&gt_two_lt_three(), &gt_minus_two_le_three());
    let expected = gt_minus_six_lt_nine();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_ge_minus_two_lt_three() {
    // (2, 3) * [-2, 3) = (-6, 9)
    let result = domain::mul(&gt_two_lt_three(), &ge_minus_two_lt_three());
    let expected = gt_minus_six_lt_nine();
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_ge_zero_le_two() {
    // [-3, -2) * [0, 2] = [-6, 0]
    let result = domain::mul(&ge_minus_three_lt_minus_two(), &ge_zero_le_two());
    let expected = ge_minus_six_le_zero();
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_ge_minus_two_le_zero() {
    // [-3, -2) * [-2, 0] = [0, 6]
    let result = domain::mul(&ge_minus_three_lt_minus_two(), &ge_minus_two_le_zero());
    let expected = ge_zero_le_six();
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_gt_minus_two_le_three() {
    // [-3, -2) * (-2, 3] = [-9, 6)
    let result = domain::mul(&ge_minus_three_lt_minus_two(), &gt_minus_two_le_three());
    let expected = ge_minus_nine_lt_six();
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_ge_minus_two_lt_three() {
    // [-3, -2) * [-2, 3) = (-9, 6]
    let result = domain::mul(&ge_minus_three_lt_minus_two(), &ge_minus_two_lt_three());
    let expected = gt_minus_nine_le_six();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_ge_zero_le_two() {
    // (-2, 2] * [0, 2] = (-4, 4]
    let result = domain::mul(&gt_minus_two_le_two(), &ge_zero_le_two());
    let expected = gt_minus_four_le_four();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_ge_minus_two_le_zero() {
    // (-2, 2] * [-2, 0] = [-4, 4)
    let result = domain::mul(&gt_minus_two_le_two(), &ge_minus_two_le_zero());
    let expected = ge_minus_four_lt_four();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_gt_minus_two_le_three() {
    // (-2, 2] * (-2, 3] = (-6, 6]
    let result = domain::mul(&gt_minus_two_le_two(), &gt_minus_two_le_three());
    let expected = gt_minus_six_le_six();
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_ge_minus_two_lt_three() {
    // (-2, 2] * [-2, 3) = (-6, 6)
    let result = domain::mul(&gt_minus_two_le_two(), &ge_minus_two_lt_three());
    let expected = gt_minus_six_lt_six();
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


// Min (4 tests).

#[test]
fn min_pos_nonneg() {
    // min((0, +inf), [0, +inf)) = [0, +inf)
    let result = domain::min(&domain::pos_dom(), &domain::nonneg_dom());
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn min_nonpos_neg() {
    // min((-inf, 0], (-inf, 0)) = (-inf, 0)
    let result = domain::min(&domain::nonpos_dom(), &domain::neg_dom());
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn min_ge_minus_nine_lt_six_gt_minus_nine_le_six() {
    // min([-9, 6), (-9, 6]) = [-9, 6)
    let result = domain::min(&ge_minus_nine_lt_six(), &gt_minus_nine_le_six());
    let expected = ge_minus_nine_lt_six();
    assert!(result.eq(&expected));
}

#[test]
fn min_gt_minus_three_lt_three_ge_minus_two_le_zero() {
    // min((-3, 3), [-2, 0]) = (-3, 0] 
    let result = domain::min(&gt_minus_three_lt_three(), &ge_minus_two_le_zero());
    let expected = gt_minus_three_le_zero();
    assert!(result.eq(&expected));
}


// Max (4 tests).

#[test] 
fn max_pos_nonneg() {
    // max((0, +inf), [0, +inf)) = (0, +inf)
    let result = domain::max(&domain::pos_dom(), &domain::nonneg_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn max_nonpos_neg() {
    // max((-inf, 0], (-inf, 0)) = (-inf, 0]
    let result = domain::max(&domain::nonpos_dom(), &domain::neg_dom());
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn max_ge_minus_nine_lt_six_gt_minus_nine_le_six() {
    // max([-9, 6), (-9, 6]) = (-9, 6]
    let result = domain::max(&ge_minus_nine_lt_six(), &gt_minus_nine_le_six());
    let expected = gt_minus_nine_le_six();
    assert!(result.eq(&expected));
}

#[test]
fn max_gt_minus_three_lt_three_ge_minus_two_le_zero() {
    // max((-3, 3), [-2, 0]) = [-2, 3)
    let result = domain::max(&gt_minus_three_lt_three(), &ge_minus_two_le_zero());
    let expected = ge_minus_two_lt_three();
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



/* Checkers */


// Is zero? (4 tests).

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


// Is one? (4 tests).

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


// Is positive? (6 tests).

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


// Is non-negative? (7 tests).

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


// Is non-positive? (7 tests).

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


// Is negative? (7 tests).

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


// Does not contain zero? (9 tests).

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
