/*!
Tests for extended interval arithmetic.
!*/

mod test_domain {

use egg_pre_dcp;
use egg_pre_dcp::CC;
use egg_pre_dcp::CO;
use egg_pre_dcp::CI;
use egg_pre_dcp::OC;
use egg_pre_dcp::OO;
use egg_pre_dcp::OI;

use egg_pre_dcp::domain;
use domain::Domain as Domain; 



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
    let result = domain::neg(&OO!(2.0, 3.0));
    let expected = OO!(-3.0, -2.0);
    assert!(result.eq(&expected));
}


// Absolute value (6 tests).

#[test]
fn abs_gt_two_lt_three() {
    // abs((2, 3)) = (2, 3)
    let result = domain::abs(&OO!(2.0, 3.0));
    let expected = OO!(2.0, 3.0);
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_three_lt_minus_two() {
    // abs((-3, -2)) = (2, 3)
    let result = domain::abs(&OO!(-3.0, -2.0));
    let expected = OO!(2.0, 3.0);
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_two_lt_three() {
    // abs((-2, 3)) = [0, 3)
    let result = domain::abs(&OO!(-2.0, 3.0));
    let expected = CO!(0.0, 3.0);
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_three_lt_two() {
    // abs((-3, 2)) = [0, 3)
    let result = domain::abs(&OO!(-3.0, 2.0));
    let expected = CO!(0.0, 3.0);
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_two_le_two() {
    // abs((-2, 2]) = [0, 2]
    let result = domain::abs(&OC!(-2.0, 2.0));
    let expected = CC!(0.0, 2.0);
    assert!(result.eq(&expected));
}

#[test]
fn abs_gt_minus_two_lt_two() {
    // abs((-2, 2)) = [0, 2)
    let result = domain::abs(&OO!(-2.0, 2.0));
    let expected = CO!(0.0, 2.0);
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
    let result = domain::sqrt(&OO!(2.0, 3.0));
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
    let result = domain::log(&CI!(1.0));
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_gt_one() {
    // log((1, +inf)) = (0, +inf)
    let result = domain::log(&OI!(1.0));
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_ge_zero_le_one() {
    // log([0, 1]) = (-inf, 0]
    let result = domain::log(&CC!(0.0, 1.0));
    let expected = domain::nonpos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_ge_zero_lt_one() {
    // log([0, 1)) = (-inf, 0)
    let result = domain::log(&CO!(0.0, 1.0));
    let expected = domain::neg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn log_gt_two_lt_three_subseteq() {
    // log((2, 3)) \subseteq (0.69, 1.10)
    let result = domain::log(&OO!(2.0, 3.0));
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
    let result = domain::exp(&OO!(2.0, 3.0));
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
    let result = domain::add(&OC!(-2.0, 2.0), &CO!(0.0, 1.0));
    let expected = OO!(-2.0, 3.0);
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
    let result = domain::sub(&OO!(-2.0, 3.0), &CC!(0.0, 1.0));
    let expected = OO!(-3.0, 3.0);
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
    let result = domain::mul(&OO!(2.0, 3.0), &OO!(2.0, 3.0));
    let expected = OO!(4.0, 9.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_gt_minus_three_lt_minus_two() {
    // [-3, -2) * (-3, -2) = (4, 9)
    let result = domain::mul(&CO!(-3.0, -2.0), &OO!(-3.0, -2.0));
    let expected = OO!(4.0, 9.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_ge_zero_le_two() {
    // (2, 3) * [0, 2] = [0, 6)
    let result = domain::mul(&OO!(2.0, 3.0), &CC!(0.0, 2.0));
    let expected = CO!(0.0, 6.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_ge_minus_two_le_zero() {
    // (2, 3) * [-2, 0] = (-6, 0]
    let result = domain::mul(&OO!(2.0, 3.0), &CC!(-2.0, 0.0));
    let expected = OC!(-6.0, 0.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_gt_minus_two_le_three() {
    // (2, 3) * (-2, 3] = (-6, 9)
    let result = domain::mul(&OO!(2.0, 3.0), &OC!(-2.0, 3.0));
    let expected = OO!(-6.0, 9.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_two_lt_three_ge_minus_two_lt_three() {
    // (2, 3) * [-2, 3) = (-6, 9)
    let result = domain::mul(&OO!(2.0, 3.0), &CO!(-2.0, 3.0));
    let expected = OO!(-6.0, 9.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_ge_zero_le_two() {
    // [-3, -2) * [0, 2] = [-6, 0]
    let result = domain::mul(&CO!(-3.0, -2.0), &CC!(0.0, 2.0));
    let expected = CC!(-6.0, 0.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_ge_minus_two_le_zero() {
    // [-3, -2) * [-2, 0] = [0, 6]
    let result = domain::mul(&CO!(-3.0, -2.0), &CC!(-2.0, 0.0));
    let expected = CC!(0.0, 6.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_gt_minus_two_le_three() {
    // [-3, -2) * (-2, 3] = [-9, 6)
    let result = domain::mul(&CO!(-3.0, -2.0), &OC!(-2.0, 3.0));
    let expected = CO!(-9.0, 6.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_ge_minus_three_lt_minus_two_ge_minus_two_lt_three() {
    // [-3, -2) * [-2, 3) = (-9, 6]
    let result = domain::mul(&CO!(-3.0, -2.0), &CO!(-2.0, 3.0));
    let expected = OC!(-9.0, 6.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_ge_zero_le_two() {
    // (-2, 2] * [0, 2] = (-4, 4]
    let result = domain::mul(&OC!(-2.0, 2.0), &CC!(0.0, 2.0));
    let expected = OC!(-4.0, 4.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_ge_minus_two_le_zero() {
    // (-2, 2] * [-2, 0] = [-4, 4)
    let result = domain::mul(&OC!(-2.0, 2.0), &CC!(-2.0, 0.0));
    let expected = CO!(-4.0, 4.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_gt_minus_two_le_three() {
    // (-2, 2] * (-2, 3] = (-6, 6]
    let result = domain::mul(&OC!(-2.0, 2.0), &OC!(-2.0, 3.0));
    let expected = OC!(-6.0, 6.0);
    assert!(result.eq(&expected));
}

#[test]
fn mul_gt_minus_two_le_two_ge_minus_two_lt_three() {
    // (-2, 2] * [-2, 3) = (-6, 6)
    let result = domain::mul(&OC!(-2.0, 2.0), &CO!(-2.0, 3.0));
    let expected = OO!(-6.0, 6.0);
    assert!(result.eq(&expected));
}


// Division (26 tests).

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
    let result = domain::div(&domain::one_dom(), &domain::pos_dom());
    let expected = domain::pos_dom();
    assert!(result.eq(&expected));
}

#[test]
fn div_gt_two_le_four_ge_one_le_two() {
    // (2, 4] / [1, 2] = (1, 4]
    let result = domain::div(&OC!(2.0, 4.0), &CC!(1.0, 2.0));
    let expected = OC!(1.0, 4.0);
    assert!(result.eq(&expected));
}

#[test]
fn div_gt_two_le_four_ge_minus_two_le_minus_one() {
    // (2, 4] / [-2, -1] = [-4, -1)
    let result = domain::div(&OC!(2.0, 4.0), &CC!(-2.0, -1.0));
    let expected = CO!(-4.0, -1.0);
    assert!(result.eq(&expected));
}

#[test]
fn div_ge_minus_four_lt_two_ge_one_le_two() {
    // [-4, 2) / [1, 2] = [-4, 2)
    let result = domain::div(&CO!(-4.0, 2.0), &CC!(1.0, 2.0));
    let expected = CO!(-4.0, 2.0);
    assert!(result.eq(&expected));
}

#[test]
fn div_ge_minus_four_lt_two_ge_minus_two_le_minus_one() {
    // [-4, 2) / [-2, -1] = (-2, 4]
    let result = domain::div(&CO!(-4.0, 2.0), &CC!(-2.0, -1.0));
    let expected = OC!(-2.0, 4.0);
    assert!(result.eq(&expected));
}

#[test]
fn div_gt_minus_two_lt_two_ge_two_le_four() {
    // (-2, 2) / [2, 4] = (-1, 1)
    let result = domain::div(&OO!(-2.0, 2.0), &CC!(2.0, 4.0));
    let expected = OO!(-1.0, 1.0);
    assert!(result.eq(&expected));
}

#[test]
fn div_ge_zero_le_two_gt_two_lt_four() {
    // [0, 2] / (2, 4) = [0, 1)
    let result = domain::div(&CC!(0.0, 2.0), &OO!(2.0, 4.0));
    let expected = CO!(0.0, 1.0);
    assert!(result.eq(&expected));
}

#[test]
fn div_gt_minus_two_lt_two_ge_minus_two_le_minus_one() {
    // (-2, 2) / [-2, -1] = (-2, 2)
    let result = domain::div(&OO!(-2.0, 2.0), &CC!(-2.0, -1.0));
    let expected = OO!(-2.0, 2.0);
    assert!(result.eq(&expected));
}

#[test]
fn div_ge_minus_two_le_zero_gt_minus_four_lt_minus_two() {
    // [-2, 0] / (-4, -2) = [0, 1) 
    let result = domain::div(&CC!(-2.0, 0.0), &OO!(-4.0, -2.0));
    let expected = CO!(0.0, 1.0);
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
    let result = domain::min(&CO!(-9.0, 6.0), &OC!(-9.0, 6.0));
    let expected = CO!(-9.0, 6.0);
    assert!(result.eq(&expected));
}

#[test]
fn min_gt_minus_three_lt_three_ge_minus_two_le_zero() {
    // min((-3, 3), [-2, 0]) = (-3, 0] 
    let result = domain::min(&OO!(-3.0, 3.0), &CC!(-2.0, 0.0));
    let expected = OC!(-3.0, 0.0);
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
    let result = domain::max(&CO!(-9.0, 6.0), &OC!(-9.0, 6.0));
    let expected = OC!(-9.0, 6.0);
    assert!(result.eq(&expected));
}

#[test]
fn max_gt_minus_three_lt_three_ge_minus_two_le_zero() {
    // max((-3, 3), [-2, 0]) = [-2, 3)
    let result = domain::max(&OO!(-3.0, 3.0), &CC!(-2.0, 0.0));
    let expected = CO!(-2.0, 3.0);
    assert!(result.eq(&expected));
}


// Power (56 tests).

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

#[test]
fn pow_free_zero() {
    // (-inf, inf) ^ [0, 0] = [1, 1]
    let result = domain::pow(&domain::free_dom(), &domain::zero_dom());
    let expected = domain::one_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_zero_zero() {
    // [0, 0] ^ [0, 0] = [1, 1]
    let result = domain::pow(&domain::zero_dom(), &domain::zero_dom());
    let expected = domain::one_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_le_four_zero() {
    // (2, 4] ^ [0, 0] = [1, 1]
    let result = domain::pow(&OC!(2.0, 4.0), &domain::zero_dom());
    let expected = domain::one_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_minus_three_lt_minus_two_zero() {
    // [-3, -2) ^ [0, 0] = [1, 1]
    let result = domain::pow(&CO!(-3.0, -2.0), &domain::zero_dom());
    let expected = domain::one_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_free_one() {
    // (-inf, inf) ^ [1, 1] = (-inf, +inf)
    let result = domain::pow(&domain::free_dom(), &domain::one_dom());
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_zero_one() {
    // [0, 0] ^ [1, 1] = [0, 0]
    let result = domain::pow(&domain::zero_dom(), &domain::one_dom());
    let expected = domain::zero_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_le_four_one() {
    // (2, 4] ^ [1, 1] = (2, 4]
    let result = domain::pow(&OC!(2.0, 4.0), &domain::one_dom());
    let expected = OC!(2.0, 4.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_minus_three_lt_minus_two_one() {
    // [-3, -2) ^ [1, 1] = [-3, -2)
    let result = domain::pow(&CO!(-3.0, -2.0), &domain::one_dom());
    let expected = CO!(-3.0, -2.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_free_two() {
    // (-inf, inf) ^ [2, 2] = [0, +inf)
    let result = domain::pow(&domain::free_dom(), &CC!(2.0, 2.0));
    let expected = domain::nonneg_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_zero_two() {
    // [0, 0] ^ [2, 2] = [0, 0]
    let result = domain::pow(&domain::zero_dom(), &CC!(2.0, 2.0));
    let expected = domain::zero_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_le_four_two() {
    // (2, 4] ^ [2, 2] = (4, 16]
    let result = domain::pow(&OC!(2.0, 4.0), &CC!(2.0, 2.0));
    let expected = OC!(4.0, 16.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_minus_three_lt_minus_two_two() {
    // [-3, -2) ^ [2, 2] = (4, 9]
    let result = domain::pow(&CO!(-3.0, -2.0), &CC!(2.0, 2.0));
    let expected = OC!(4.0, 9.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_le_four_four() {
    // (2, 4] ^ [4, 4] = (16, 256]
    let result = domain::pow(&OC!(2.0, 4.0), &CC!(4.0, 4.0));
    let expected = OC!(16.0, 256.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_minus_three_lt_minus_two_four() {
    // [-3, -2) ^ [4, 4] = (16, 81]
    let result = domain::pow(&CO!(-3.0, -2.0), &CC!(4.0, 4.0));
    let expected = OC!(16.0, 81.0);
    assert!(result.eq(&expected));
} 

#[test]
fn pow_gt_minus_two_le_four_ge_two_lt_three() {
    // (-2, 4] ^ [2, 3) = (-inf, +inf)
    let result = domain::pow(&OC!(-2.0, 4.0), &CO!(2.0, 3.0));
    let expected = domain::free_dom();
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_le_four_ge_two_lt_three() {
    // (2, 4] ^ [2, 3) = (4, 64)
    let result = domain::pow(&OC!(2.0, 4.0), &CO!(2.0, 3.0));
    let expected = OO!(4.0, 64.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_le_four_ge_minus_three_lt_minus_two() {
    // (2, 4] ^ [-3, -2) = [0.015625, 0.25)
    let result = domain::pow(&OC!(2.0, 4.0), &CO!(-3.0, -2.0));
    let expected = CO!(0.015625, 0.25);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_le_four_ge_minus_three_lt_two() {
    // (2, 4] ^ [-3, 2) = [0.015625, 16)
    let result = domain::pow(&OC!(2.0, 4.0), &CO!(-3.0, 2.0));
    let expected = CO!(0.015625, 16.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_lt_four_ge_minus_three_le_zero() {
    // (2, 4) ^ [-3, 0] = (0.015625, 1]
    let result = domain::pow(&OO!(2.0, 4.0), &CC!(-3.0, 0.0));
    let expected = OC!(0.015625, 1.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_two_lt_four_ge_zero_lt_two() {
    // (2, 4) ^ [0, 2) = [1, 16)
    let result = domain::pow(&OO!(2.0, 4.0), &CO!(0.0, 2.0));
    let expected = CO!(1.0, 16.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_point_one_two_five_le_point_five_ge_two_lt_three() {
    // (0.125, 0.5] ^ [2, 3) = (0.001953125, 0.25]
    let result = domain::pow(&OC!(0.125, 0.5), &CO!(2.0, 3.0));
    let expected = OC!(0.001953125, 0.25);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_point_one_two_five_le_point_five_ge_minus_three_lt_minus_two() {
    // (0.125, 0.5] ^ [-3, -2) = (4, 512)
    let result = domain::pow(&OC!(0.125, 0.5), &CO!(-3.0, -2.0));
    let expected = OO!(4.0, 512.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_point_one_two_five_le_point_five_ge_minus_three_lt_two() {
    // (0.125, 0.5] ^ [-3, 2) = (0.015625, 512)
    let result = domain::pow(&OC!(0.125, 0.5), &CO!(-3.0, 2.0));
    let expected = OO!(0.015625, 512.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_point_one_two_five_le_point_five_ge_minus_three_le_zero() {
    // (0.125, 0.5] ^ [-3, 0] = [1, 512)
    let result = domain::pow(&OC!(0.125, 0.5), &CC!(-3.0, 0.0));
    let expected = CO!(1.0, 512.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_gt_point_one_two_five_le_point_five_ge_zero_lt_two() {
    // (0.125, 0.5] ^ [0, 2) = (0.015625, 1]
    let result = domain::pow(&OC!(0.125, 0.5), &CO!(0.0, 2.0));
    let expected = OC!(0.015625, 1.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_point_five_lt_four_ge_two_lt_three() {
    // [0.5, 4) ^ [2, 3) = (0.125, 64)
    let result = domain::pow(&CO!(0.5, 4.0), &CO!(2.0, 3.0));
    let expected = OO!(0.125, 64.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_point_five_lt_four_ge_minus_three_lt_minus_two() {
    // [0.5, 4) ^ [-3, -2) = (0.015625, 8]
    let result = domain::pow(&CO!(0.5, 4.0), &CO!(-3.0, -2.0));
    let expected = OC!(0.015625, 8.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_point_five_lt_four_ge_minus_three_lt_two() {
    // [0.5, 4) ^ [-3, 2) = (0.015625, 16)
    let result = domain::pow(&CO!(0.5, 4.0), &CO!(-3.0, 2.0));
    let expected = OO!(0.015625, 16.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_point_five_lt_four_ge_minus_three_lt_zero() {
    // [0.5, 4) ^ [-3, 0) = (0.015625, 8]
    let result = domain::pow(&CO!(0.5, 4.0), &CO!(-3.0, 0.0));
    let expected = OC!(0.015625, 8.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_point_five_lt_four_ge_zero_lt_two() {
    // [0.5, 4) ^ [0, 2) = (0.25, 16)
    let result = domain::pow(&CO!(0.5, 4.0), &CO!(0.0, 2.0));
    let expected = OO!(0.25, 16.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_zero_lt_four_ge_two_lt_three() {
    // [0, 4) ^ [2, 3) = [0, 64)
    let result = domain::pow(&CO!(0.0, 4.0), &CO!(2.0, 3.0));
    let expected = CO!(0.0, 64.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_zero_lt_four_ge_minus_three_lt_minus_two() {
    // [0, 4) ^ [-3, -2) = (0.015625, +inf)
    let result = domain::pow(&CO!(0.0, 4.0), &CO!(-3.0, -2.0));
    let expected = OI!(0.015625);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_zero_lt_four_ge_minus_three_lt_two() {
    // [0, 4) ^ [-3, 2) = [0, +inf)
    let result = domain::pow(&CO!(0.0, 4.0), &CO!(-3.0, 2.0));
    let expected = CI!(0.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_zero_lt_four_ge_minus_three_lt_zero() {
    // [0, 4) ^ [-3, 0) = (0.015625, +inf)
    let result = domain::pow(&CO!(0.0, 4.0), &CO!(-3.0, 0.0));
    let expected = OI!(0.015625);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_zero_lt_four_ge_zero_lt_two() {
    // [0, 4) ^ [0, 2) = [0, 16)
    let result = domain::pow(&CO!(0.0, 4.0), &CO!(0.0, 2.0));
    let expected = CO!(0.0, 16.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_one_lt_four_ge_two_lt_three() {
    // [1, 4) ^ [2, 3) = [1, 64)
    let result = domain::pow(&CO!(1.0, 4.0), &CO!(2.0, 3.0));
    let expected = CO!(1.0, 64.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_one_lt_four_ge_minus_three_lt_minus_two() {
    // [1, 4) ^ [-3, -2) = (0.015625, 1]
    let result = domain::pow(&CO!(1.0, 4.0), &CO!(-3.0, -2.0));
    let expected = OC!(0.015625, 1.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_one_lt_four_ge_minus_three_lt_two() {
    // [1, 4) ^ [-3, 2) = (0.015625, 16)
    let result = domain::pow(&CO!(1.0, 4.0), &CO!(-3.0, 2.0));
    let expected = OO!(0.015625, 16.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_one_lt_four_ge_minus_three_lt_zero() {
    // [1, 4) ^ [-3, 0) = (0.015625, 1)
    let result = domain::pow(&CO!(1.0, 4.0), &CO!(-3.0, 0.0));
    let expected = OC!(0.015625, 1.0);
    assert!(result.eq(&expected));
}

#[test]
fn pow_ge_one_lt_four_ge_zero_lt_two() {
    // [1, 4) ^ [0, 2) = [1, 16)
    let result = domain::pow(&CO!(1.0, 4.0), &CO!(0.0, 2.0));
    let expected = CO!(1.0, 16.0);
    assert!(result.eq(&expected));
}



/* Checkers */


// Is zero? (4 tests).

#[test]
fn is_zero_zero() {
    // [0, 0] is zero
    assert!(domain::is_zero(&domain::zero_dom()));
}

#[test]
fn not_is_zero_one() {
    // [1, 1] is not zero
    assert!(!domain::is_zero(&domain::one_dom()));
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
    assert!(domain::is_one(&domain::one_dom()));
}

#[test]
fn not_is_one_zero() {
    // [0, 0] is not one
    assert!(!domain::is_one(&domain::zero_dom()));
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
    assert!(domain::is_pos(&domain::one_dom()));
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
    assert!(!domain::is_pos(&domain::zero_dom()));
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
    assert!(domain::is_nonneg(&domain::zero_dom()));
}

#[test]
fn is_nonneg_one() {
    // [1, 1] is non-negative
    assert!(domain::is_nonneg(&domain::one_dom()));
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
    assert!(domain::is_nonpos(&domain::zero_dom()));
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
    assert!(!domain::is_nonpos(&domain::one_dom()));
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
    assert!(!domain::is_neg(&domain::zero_dom()));
}

#[test]
fn not_is_neg_one() {
    // [1, 1] is not negative
    assert!(!domain::is_neg(&domain::one_dom()));
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
    assert!(domain::does_not_contain_zero(&domain::one_dom()));
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
    assert!(!domain::does_not_contain_zero(&domain::zero_dom()));
}

}
