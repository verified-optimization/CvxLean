use egg::{rewrite as rw, *};

use crate::optimization;
use optimization::Optimization as Optimization;
use optimization::Meta as Meta;
use optimization::is_gt_zero as is_gt_zero;
use optimization::is_not_zero as is_not_zero;
use optimization::not_has_log as not_has_log;

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![

    /* Objective function rules. */

    // NOTE(RFM): Acceptable because it can only be applied once.
    rw!("map_objFun_log"; "(objFun ?a)" => "(objFun (log ?a))" 
        if is_gt_zero("?a") if not_has_log("?a")),


    /* Equality rules. */

    // rw!("eq-add"; "(eq ?a (add ?b ?c))" => "(eq (sub ?a ?c) ?b)"),

    // rw!("eq-sub"; "(eq ?a (sub ?b ?c))" => "(eq (add ?a ?c) ?b)"),

    // rw!("eq-mul"; "(eq ?a (mul ?b ?c))" => "(eq (div ?a ?c) ?b)" 
    //     if is_not_zero("?c")),

    // rw!("eq-div"; "(eq ?a (div ?b ?c))" => "(eq (mul ?a ?c) ?b)" 
    //     if is_not_zero("?c")),

    // rw!("eq-sub-zero"; "(eq ?a ?b)" => "(eq (sub ?a ?b) 0)"
    //     if is_not_zero("?b")),

    // rw!("eq-div-one"; "(eq ?a ?b)" => "(eq (div ?a ?b) 1)" 
    //     if is_not_zero("?b") if is_not_one("?b")),
    
    // NOTE(RFM): Acceptable because it can only be applied once.
    rw!("log_eq_log"; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b") 
        if not_has_log("?a") if not_has_log("?b")),


    /* Less than or equal rules. */

    rw!("le_sub_iff_add_le"; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)"),

    // rw!("le-add"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)"),

    // rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
    //     if is_not_zero("?c")),

    rw!("div_le_iff"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_gt_zero("?c")),
    
    rw!("div_le_iff-rev"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_gt_zero("?c")),

    // rw!("le-div"; "(le ?a (div ?b ?c))" => "(le (mul ?a ?c) ?b)" 
    //     if is_not_zero("?c")),

    // rw!("le-sub-zero"; "(le ?a ?b)" => "(le (sub ?a ?b) 0)" 
    //     if is_not_zero("?b")),

    // NOTE(RFM): div-le-one? 
    // rw!("div_le_one-rev"; "(le ?a ?b)" => "(le (div ?a ?b) 1)" 
    //     if is_not_zero("?b") if is_not_one("?b")),

    rw!("log_le_log"; "(le (log ?a) (log ?b))" => "(le ?a ?b)" 
       if is_gt_zero("?a") if is_gt_zero("?b")),  

    // NOTE(RFM): Acceptable because it can only be applied once.
    rw!("log_le_log-rev"; "(le ?a ?b)" => "(le (log ?a) (log ?b))"
        if is_gt_zero("?a") if is_gt_zero("?b") 
        if not_has_log("?a") if not_has_log("?b")),


    /* Field rules. */

    rw!("one_mul"; "(mul 1 ?a)" => "?a"),

    rw!("one_mul-rev"; "?a" => "(mul 1 ?a)"),

    rw!("add_comm"; "(add ?a ?b)" => "(add ?b ?a)"), 

    rw!("add_assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
    
    rw!("mul_comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("mul_assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),

    rw!("add_sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),

    rw!("add_mul"; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))"),

    rw!("add_mul-rev"; "(add (mul ?a ?c) (mul ?b ?c))" => "(mul (add ?a ?b) ?c)"),

    rw!("mul_add"; "(mul ?a (add ?b ?c))" => "(add (mul ?a ?b) (mul ?a ?c))"),
    
    // rw!("mul-sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),

    // rw!("sub-self"; "(sub ?a ?a)" => "0"),

    rw!("mul_sub-rev"; "(sub (mul ?a ?b) (mul ?a ?c))" => 
        "(mul ?a (sub ?b ?c))"),

    // rw!("sub-mul-right"; "(sub (mul ?a ?b) (mul ?c ?b))" => 
    //     "(mul (sub ?a ?c) ?b)"),

    // rw!("sub-mul-same-right"; "(sub ?a (mul ?b ?a))" => "(mul ?a (sub 1 ?b))"),

    // rw!("sub-mul-same-left"; "(sub (mul ?a ?b) ?a)" => "(mul ?a (sub ?b 1))"),

    rw!("add_div"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))"),

    // rw!("add-div"; "(add (div ?a ?b) (div ?c ?b))" => "(div (add ?a ?c) ?b)"),

    // rw!("div-sub"; "(div (sub ?a ?b) ?c)" => "(sub (div ?a ?c) (div ?b ?c))" 
    //     if is_not_zero("?c")),

    rw!("mul_div"; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)"),

    rw!("mul_div-rev"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),

    rw!("div_self"; "(div ?a ?a)" => "1" if is_not_zero("?a")),


    /* Power and square root rules. */

    // rw!("pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"),

    // rw!("mul-pow"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"),

    // rw!("pow-sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" 
    //     if is_not_zero("?a")),

    rw!("div_pow_eq_mul_pow_neg"; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))"
        if is_gt_zero("?b")),

    // rw!("div-pow-same-right"; "(div ?a (pow ?a ?b))" => "(pow ?a (sub 1 ?b))"),

    // rw!("div-pow-same-left"; "(div (pow ?a ?b) ?a)" => "(pow ?a (sub ?b 1))"),

    rw!("sqrt_eq_rpow"; "(sqrt ?a)" => "(pow ?a 0.5)"),


    /* Exponential and logarithm rules. */

    rw!("exp_add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),

    rw!("exp_add-rev"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    rw!("exp_sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),

    rw!("exp_sub-rev"; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))"),
    
    rw!("exp_mul"; "(exp (mul ?a ?b))" => "(pow (exp ?a) ?b)"),

    rw!("exp_mul-rev"; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))"),

    // NOTE(RFM): exp_neg_eq_one_div_div?
    rw!("exp_neg_eq_one_div-rev"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),

    rw!("exp_log"; "(exp (log ?a))" => "?a" if is_gt_zero("?a")),

    rw!("log_mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log_div"; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log_exp"; "(log (exp ?a))" => "?a"),  
] }

#[allow(unused)]
pub fn simple_example_rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_gt_zero("?c")),
    
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_gt_zero("?c")),
    
    rw!("inv-exp"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),
] }
