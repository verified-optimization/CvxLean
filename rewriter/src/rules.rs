use egg::{rewrite as rw, *};

use crate::optimization;
use optimization::Optimization as Optimization;
use optimization::Meta as Meta;
use optimization::is_not_zero as is_not_zero;
use optimization::is_not_one as is_not_one;
use optimization::is_gt_zero as is_gt_zero;
use optimization::not_has_log as not_has_log;

pub fn rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("eq-add"; "(eq ?a (add ?b ?c))" => "(eq (sub ?a ?c) ?b)"),

    rw!("eq-sub"; "(eq ?a (sub ?b ?c))" => "(eq (add ?a ?c) ?b)"),

    rw!("eq-mul"; "(eq ?a (mul ?b ?c))" => "(eq (div ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("eq-div"; "(eq ?a (div ?b ?c))" => "(eq (mul ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("eq-sub-zero"; "(eq ?a ?b)" => "(eq (sub ?a ?b) 0)"
        if is_not_zero("?b")),

    rw!("eq-div-one"; "(eq ?a ?b)" => "(eq (div ?a ?b) 1)" 
        if is_not_zero("?b") if is_not_one("?b")),

    rw!("le-sub"; "(le ?a (sub ?b ?c))" => "(le (add ?a ?c) ?b)"),

    rw!("le-add"; "(le ?a (add ?b ?c))" => "(le (sub ?a ?c) ?b)"),

    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_not_zero("?c")),

    // NOTE(RFM): The b != 1 condition is to avoid infinite chains in 
    // combination with le-div-one.
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_not_zero("?c") if is_not_one("?b")),

    rw!("le-div"; "(le ?a (div ?b ?c))" => "(le (mul ?a ?c) ?b)" 
        if is_not_zero("?c")),

    rw!("le-sub-zero"; "(le ?a ?b)" => "(le (sub ?a ?b) 0)" 
        if is_not_zero("?b")),

    rw!("le-div-one"; "(le ?a ?b)" => "(le (div ?a ?b) 1)" 
        if is_not_zero("?b") if is_not_one("?b")),

    rw!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"), 

    rw!("add-assoc"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
    
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("mul-assoc"; "(mul (mul ?a ?b) ?c)" => "(mul ?a (mul ?b ?c))"),

    rw!("add-sub"; "(add ?a (sub ?b ?c))" => "(sub (add ?a ?b) ?c)"),

    rw!("add-mul"; "(mul (add ?a ?b) ?c)" => "(add (mul ?a ?c) (mul ?b ?c))"),

    rw!("mul-sub"; "(mul ?a (sub ?b ?c))" => "(sub (mul ?a ?b) (mul ?a ?c))"),

    // NOTE(RFM): Testing this.
    rw!("sub-self"; "(sub ?a ?a)" => "0"),

    rw!("sub-mul-left"; "(sub (mul ?a ?b) (mul ?a ?c))" => 
        "(mul ?a (sub ?b ?c))"),

    rw!("sub-mul-right"; "(sub (mul ?a ?b) (mul ?c ?b))" => 
        "(mul (sub ?a ?c) ?b)"),

    rw!("sub-mul-same-right"; "(sub ?a (mul ?b ?a))" => "(mul ?a (sub 1 ?b))"),

    rw!("sub-mul-same-left"; "(sub (mul ?a ?b) ?a)" => "(mul ?a (sub ?b 1))"),

    rw!("mul-div"; "(mul ?a (div ?b ?c))" => "(div (mul ?a ?b) ?c)" 
        if is_not_zero("?c")),

    rw!("div-mul"; "(div (mul ?a ?b) ?c)" => "(mul ?a (div ?b ?c))"),
    
    rw!("div-add"; "(div (add ?a ?b) ?c)" => "(add (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    rw!("add-div"; "(add (div ?a ?b) (div ?c ?b))" => "(div (add ?a ?c) ?b)"),

    rw!("div-sub"; "(div (sub ?a ?b) ?c)" => "(sub (div ?a ?c) (div ?b ?c))" 
        if is_not_zero("?c")),

    rw!("pow-add"; "(pow ?a (add ?b ?c))" => "(mul (pow ?a ?b) (pow ?a ?c))"),

    rw!("mul-pow"; "(mul (pow ?a ?b) (pow ?a ?c))" => "(pow ?a (add ?b ?c))"),

    rw!("pow-sub"; "(pow ?a (sub ?b ?c))" => "(div (pow ?a ?b) (pow ?a ?c))" 
        if is_not_zero("?a")),

    rw!("div-pow"; "(div ?a (pow ?b ?c))" => "(mul ?a (pow ?b (neg ?c)))"
        if is_gt_zero("?b")),

    rw!("div-pow-same-right"; "(div ?a (pow ?a ?b))" => "(pow ?a (sub 1 ?b))"),

    rw!("div-pow-same-left"; "(div (pow ?a ?b) ?a)" => "(pow ?a (sub ?b 1))"),

    rw!("sqrt_eq_rpow"; "(sqrt ?a)" => "(pow ?a 0.5)"),

    rw!("exp-add"; "(exp (add ?a ?b))" => "(mul (exp ?a) (exp ?b))"),

    rw!("mul-exp"; "(mul (exp ?a) (exp ?b))" => "(exp (add ?a ?b))"),

    rw!("exp-sub"; "(exp (sub ?a ?b))" => "(div (exp ?a) (exp ?b))"),

    rw!("div-exp"; "(div (exp ?a) (exp ?b))" => "(exp (sub ?a ?b))"),
    
    rw!("inv-exp"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),

    rw!("pow-exp"; "(pow (exp ?a) ?b)" => "(exp (mul ?a ?b))"),

    rw!("log-mul"; "(log (mul ?a ?b))" => "(add (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log-div"; "(log (div ?a ?b))" => "(sub (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b")),

    rw!("log-exp"; "(log (exp ?a))" => "?a"),

    // NOTE(RFM): The following two rewrites are acceptable because they 
    // rewrite Props so it is not affecting the curvature of the underlying 
    // expressions.
    rw!("eq-log"; "(eq ?a ?b)" => "(eq (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b") 
        if not_has_log("?a") if not_has_log("?b")),

    rw!("le-log"; "(le ?a ?b)" => "(le (log ?a) (log ?b))" 
        if is_gt_zero("?a") if is_gt_zero("?b") 
        if not_has_log("?a") if not_has_log("?b")),

    // NOTE(RFM): The following rewrite is acceptable because we enforce log 
    // to only be applied once. Otherwise, we would have incompatible 
    // curvatures in the same e-class.
    rw!("map-objFun-log"; "(objFun ?a)" => "(objFun (log ?a))" 
        if is_gt_zero("?a") if not_has_log("?a")),

    
] }

pub fn example_rules() -> Vec<Rewrite<Optimization, Meta>> { vec![
    rw!("mul-comm"; "(mul ?a ?b)" => "(mul ?b ?a)"),

    rw!("le-mul"; "(le ?a (mul ?b ?c))" => "(le (div ?a ?c) ?b)" 
        if is_not_zero("?c")),
    
    rw!("le-mul-rev"; "(le (div ?a ?c) ?b)" => "(le ?a (mul ?b ?c))" 
        if is_not_zero("?c")),
    
    rw!("inv-exp"; "(div 1 (exp ?a))" => "(exp (neg ?a))"),
] }