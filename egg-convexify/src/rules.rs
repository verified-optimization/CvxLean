use egg::{rewrite as rw, *};

use crate::optimization;
use optimization::Optimization as Optimization;
use optimization::Meta as Meta;
use optimization::is_gt_zero as is_gt_zero;
use optimization::is_ge_zero as is_ge_zero;
use optimization::is_le_zero as is_le_zero;
use optimization::is_not_zero as is_not_zero;
use optimization::is_nat as is_nat;

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![

    /* Objective function rules. */

    rw!("map_objFun_log"; "(objFun ?a)" => "(objFun (log ?a))"
        if is_gt_zero("?a")),

    rw!("map_objFun_sq"; "(objFun ?a)" => "(objFun (pow ?a 2))"
        if is_ge_zero("?a")),


    /* Equality rules. */
    // NOTE: many more rules could apply here, but in our examples, equalities
    // were either already affine or required applying logarithms to remove
    // exponentials and make them affine.

    rw!("log_eq_log"; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b")),


    /* Less than or equal rules. */

    rw!("le_sub_iff_add_le"; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)"),

    rw!("le_sub_iff_add_le-rev"; "(le (add ?a ?c) ?b)" => "(le ?a (sub ?b ?c))"),

    rw!("sub_le_iff_le_add"; "(le (sub ?a ?c) ?b)" => "(le ?a (add ?b ?c))"),

    rw!("sub_le_iff_le_add-rev"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)"),

    rw!("div_le_iff"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))"
        if is_gt_zero("?c")),

    rw!("div_le_iff-rev"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)"
        if is_gt_zero("?c")),

    rw!("log_le_log"; "(le (log ?a) (log ?b))" => "(le ?a ?b)"
       if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log_le_log-rev"; "(le ?a ?b)" => "(le (log ?a) (log ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("pow_two_le_pow_two"; "(le (pow ?a 2) (pow ?b 2))" => "(le ?a ?b)"
        if is_ge_zero("?a") if is_ge_zero("?b")),

    rw!("pow_two_le_pow_two-rev"; "(le ?a ?b)" => "(le (pow ?a 2) (pow ?b 2))"
        if is_ge_zero("?a") if is_ge_zero("?b")),


    /* Field rules. */

    rw!("neg_neg"; "(neg (neg ?a))" => "?a"),

    rw!("add_zero"; "(add ?a 0)" => "?a"),

    rw!("add_comm"; "(add ?a ?b)" => "(add ?b ?a)"),

    rw!("add_assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),

    rw!("sub_self"; "(sub ?a ?a)" => "0"),

    rw!("one_mul"; "(mul 1 ?a)" => "?a"),

    rw!("one_mul-rev"; "?a" => "(mul 1 ?a)"),

    rw!("mul_zero"; "(mul 0 ?a)" => "0"),

    rw!("mul_comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("mul_assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),

    rw!("sub_eq_add_neg"; "(sub ?a ?b)" => "(add ?a (neg ?b))"),

    rw!("sub_eq_add_neg-rev"; "(add ?a (neg ?b))" => "(sub ?a ?b)"),

    rw!("add_sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),

    rw!("add_sub-rev"; "(sub (add ?a ?b) ?c)" => "(add ?a (sub ?b ?c))"),

    rw!("add_mul"; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))"),

    rw!("add_mul-rev"; "(add (mul ?a ?c) (mul ?b ?c))" => "(mul (add ?a ?b) ?c)"),

    rw!("mul_add"; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))"),

    rw!("mul_add-rev"; "(add (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (add ?b ?c))"),

    rw!("mul_sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),

    rw!("mul_sub-rev"; "(sub (mul ?a ?b) (mul ?a ?c))" => "(mul ?a (sub ?b ?c))"),

    rw!("div_one"; "(div ?a 1)" => "?a"),

    rw!("add_div"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))"),

    rw!("add_div-rev"; "(add (div ?a ?c) (div ?b ?c))" => "(div (add ?a ?b) ?c)"),

    rw!("mul_div"; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)"),

    rw!("mul_div-rev"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),

    rw!("div_mul"; "(mul (div ?a ?b) ?c)" => "(div ?a (div ?b ?c))"
        if is_not_zero("?b") if is_not_zero("?c")),

    rw!("div_mul-rev"; "(div ?a (div ?b ?c))" => "(mul (div ?a ?b) ?c)"
        if is_not_zero("?b") if is_not_zero("?c")),

    rw!("mul_div_mul_left"; "(div (mul ?c ?a) (mul ?c ?b))" => "(div ?a ?b)"
        if is_not_zero("?c")),

    rw!("div_div"; "(div (div ?a ?b) ?c)" => "(div ?a (mul ?b ?c))"
        if is_not_zero("?b") if is_not_zero("?c")),

    rw!("div_div-rev"; "(div ?a (mul ?b ?c))" => "(div (div ?a ?b) ?c)"
        if is_not_zero("?b") if is_not_zero("?c")),

    rw!("div_self"; "(div ?a ?a)" => "1" if is_not_zero("?a")),

    rw!("inv_eq_one_div"; "(inv ?a)" => "(div 1 ?a)" if is_not_zero("?a")),

    rw!("inv_inv"; "(inv (inv ?a))" => "?a" if is_not_zero("?a")),


    /* Power and square root rules. */

    rw!("one_pow"; "(pow 1 ?a)" => "1"),

    rw!("pow_one"; "(pow ?a 1)" => "?a"),

    rw!("pow_add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"
        if is_gt_zero("?a")),

    rw!("pow_add-rev"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"
        if is_gt_zero("?a")),

    rw!("mul_pow"; "(pow (mul ?a ?b) ?n)" => "(mul (pow ?a ?n) (pow ?b ?n))"
        if is_ge_zero("?a") if is_ge_zero("?b")),

    rw!("mul_pow-rev"; "(mul (pow ?a ?n) (pow ?b ?n))" => "(pow (mul ?a ?b) ?n)"
        if is_ge_zero("?a") if is_ge_zero("?b")),

    rw!("pow_mul"; "(pow ?a (mul ?n ?m))" => "(pow (pow ?a ?n) ?m)"
        if is_ge_zero("?a")),

    rw!("pow_mul-rev"; "(pow (pow ?a ?n) ?m)" => "(pow ?a (mul ?n ?m))"
        if is_ge_zero("?a")),

    rw!("div_pow"; "(pow (div ?a ?b) ?n)" => "(div (pow ?a ?n) (pow ?b ?n))"
        if is_ge_zero("?a") if is_gt_zero("?b")),

    rw!("div_pow-rev"; "(div (pow ?a ?n) (pow ?b ?n))" => "(pow (div ?a ?b) ?n)"
        if is_ge_zero("?a") if is_gt_zero("?b")),

    rw!("pow_sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))"
        if is_gt_zero("?a")),

    rw!("pow_sub-rev"; "(div (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (sub ?b ?c))"
        if is_gt_zero("?a")),

    rw!("div_pow_eq_mul_pow_neg"; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))"
        if is_gt_zero("?b")),

    rw!("div_pow_eq_mul_pow_neg-rev"; "(mul ?a (pow ?b (neg ?c)))" => "(div ?a (pow ?b ?c))"
        if is_gt_zero("?b")),

    rw!("one_div_eq_pow_neg_one"; "(div 1 ?a)" => "(pow ?a (neg 1))"
        if is_gt_zero("?a")),

    rw!("sqrt_eq_rpow"; "(sqrt ?a)" => "(pow ?a 0.5)"),

    rw!("sqrt_eq_rpow-rev"; "(pow ?a 0.5)" => "(sqrt ?a)"),

    rw!("sqrt_mul"; "(sqrt (mul ?a ?b))" => "(mul (sqrt ?a) (sqrt ?b))"
        if is_ge_zero("?a") if is_ge_zero("?b")),

    rw!("sqrt_mul-rev"; "(mul (sqrt ?a) (sqrt ?b))" => "(sqrt (mul ?a ?b))"
        if is_ge_zero("?a") if is_ge_zero("?b")),

    rw!("pow_two"; "(pow ?a 2)" => "(mul ?a ?a)"),

    rw!("pow_two-rev"; "(mul ?a ?a)" => "(pow ?a 2)"),

    rw!("pow_half_two"; "(pow (pow ?a 0.5) 2)" => "?a" if is_ge_zero("?a")),

    rw!("pow_half_two-rev"; "?a" => "(pow (pow ?a 0.5) 2)" if is_ge_zero("?a")),

    rw!("binomial_two"; "(pow (add ?a ?b) 2)" => "(add (pow ?a 2) (add (mul 2 (mul ?a ?b)) (pow ?b 2)))"),

    rw!("rpow_eq_mul_rpow_pred"; "(pow ?a ?b)" => "(mul ?a (pow ?a (sub ?b 1)))"
        if is_not_zero("?a")),

    rw!("inv_eq_pow_neg_one"; "(inv ?a)" => "(pow ?a (neg 1))" if is_not_zero("?a")),


    /* Exponential and logarithm rules. */

    rw!("exp_add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),

    rw!("exp_add-rev"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    rw!("exp_sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),

    rw!("exp_sub-rev"; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))"),

    rw!("exp_mul"; "(exp (mul ?a ?b))" => "(pow (exp ?a) ?b)"),

    rw!("exp_mul-rev"; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))"),

    rw!("exp_neg_eq_one_div"; "(exp (neg ?a))" => "(div 1 (exp ?a))"),

    rw!("exp_neg_eq_one_div-rev"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),

    rw!("log_mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log_mul-rev"; "(add (log ?a) (log ?b))" => "(log (mul ?a ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log_div"; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log_div-rev"; "(sub (log ?a) (log ?b))" => "(log (div ?a ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log_pow"; "(log (pow ?a ?b))" => "(mul ?b (log ?a))"
        if is_gt_zero("?a")),

    rw!("log_pow-rev"; "(mul ?b (log ?a))" => "(log (pow ?a ?b))"
        if is_gt_zero("?a")),

    rw!("log_pow_nat"; "(log (pow ?a ?b))" => "(mul ?b (log ?a))"
        if is_nat("?b")),

    rw!("log_pow_nat-rev"; "(mul ?b (log ?a))" => "(log (pow ?a ?b))"
        if is_nat("?b")),

    rw!("exp_log"; "(exp (log ?a))" => "?a" if is_gt_zero("?a")),

    rw!("log_exp"; "(log (exp ?a))" => "?a"),


    /* Abs rules. */

    rw!("abs_nonneg"; "(abs ?a)" => "?a" if is_ge_zero("?a")),

    rw!("abs_nonpos"; "(abs ?a)" => "(neg ?a)" if is_le_zero("?a")),


    /* Atom folding and unfolding rules. */

    rw!("xexp_fold"; "(mul ?a (exp ?a))" => "(xexp ?a)"
        if is_ge_zero("?a")),

    rw!("xexp_unfold"; "(xexp ?a)" => "(mul ?a (exp ?a))"
        if is_ge_zero("?a")),

    rw!("entr_fold"; "(neg (mul ?a (log ?a)))" => "(entr ?a)"
        if is_gt_zero("?a")),

    rw!("entr_unfold"; "(entr ?a)" => "(neg (mul ?a (log ?a)))"
        if is_gt_zero("?a")),

    rw!("qol_fold"; "(div (pow ?a 2) ?b)" => "(qol ?a ?b)"
        if is_gt_zero("?b")),

    rw!("qol_unfold"; "(qol ?a ?b)" => "(div (pow ?a 2) ?b)"
        if is_gt_zero("?b")),

    rw!("geo_fold"; "(sqrt (mul ?a ?b))" => "(geo ?a ?b)"
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("geo_unfold"; "(geo ?a ?b)" => "(sqrt (mul ?a ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("lse_fold"; "(log (add (exp ?a) (exp ?b)))" => "(lse ?a ?b)"),

    rw!("lse_unfold"; "(lse ?a ?b)" => "(log (add (exp ?a) (exp ?b)))"),

    rw!("norm2_fold"; "(sqrt (add (pow ?a 2) (pow ?b 2)))" => "(norm2 ?a ?b)"),

    rw!("norm2_unfold"; "(norm2 ?a ?b)" => "(sqrt (add (pow ?a 2) (pow ?b 2)))"),
] }

#[allow(unused)]
pub fn simple_example_rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)"
        if is_gt_zero("?c")),

    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))"
        if is_gt_zero("?c")),

    rw!("exp_neg_eq_one_div-rev"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),
] }
