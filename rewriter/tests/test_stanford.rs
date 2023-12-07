/*!
Tests from the additional exercises in the Stanford Convex Optimization course:
https://github.com/cvxgrp/cvxbook_additional_exercises
!*/

use egg_convexify::domain;

use egg_convexify::test_util::{*};

#[test]
fn test_3_32() {
    // 1 / (x * y) = (x^-0.5)^2 / y
    //             = qol(x^-0.5, y) (this is just one possibility)
    convexify_check_expression_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
        "(div 1 (mul (var x) (var y)))");
}

#[test]
fn test_3_33() {
    // sqrt(1 + x^4 / y) = sqrt(1^2 + (x^2 / y)^2)
    //               ... = norm2(1, qol(x, y))
    // NOTE(RFM): Constant unfolding issue: x cannot be in the free domain as 
    // otherwise we cannot convert x^4 to (x^2)^2.
    convexify_check_expression_with_domain(
        vec![("x", domain::nonneg_dom()), ("y", domain::pos_dom())], 
        "(sqrt (add 1 (div (pow (var x) 4) (var y))))"
    );
}

#[test]
fn test_3_36_a() {
    // sqrt(1 + 4x^2 + 16y^2) = sqrt((2x)^2 + (sqrt(1^2 + (4y)^2))^2)
    //                    ... = norm2(2x, norm2(1, 4y))
    convexify_check_expression_with_domain(
        vec![("x", domain::nonneg_dom()), ("y", domain::nonneg_dom())], 
         "(sqrt (add 1 (add (mul 4 (pow (var x) 2)) (mul 16 (pow (var y) 2)))))");
}

// #[test]
// fn test_3_36_c() {
//     // log(e^(2x + 3) + e^(4y + 5)) = lse(2x + 3, 4y + 5) 
//     convexify_check_expression_with_domain(
//         vec![("x", domain::free_dom()), ("y", domain::free_dom())], 
//          "(log (add (exp (add (mul 2 (var x)) 3)) (exp (add (mul 4 (var y)) 5))))");
// }

#[test]
fn test_3_38_e() {
    // (sqrt(x) + sqrt(y))^2 = x + y + 2sqrt(xy)
    //                   ... = x + y + 2geo(x, y)
    convexify_check_expression_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
         "(neg (pow (add (sqrt (var x)) (sqrt (var y))) 2))");
}

#[test]
fn test_3_67() {
    // Generalizaiton of 3.28. Works for n = 3, times out for n >= 4.
    // (sqrt(x_1) + ... + sqrt(x_n))^2  
    //               ... = sum_{i <= n} x_i + 2 * sum_{i < j <= n} geo(x_i, x_j)
    let build_domain = |n| {
        if n < 2 { 
            panic!("n must be >= 2"); 
        }
        let mut v = Vec::new();
        for i in 0..n { 
            v.push((format!("x{}", i), domain::pos_dom())); 
        }
        v
    };
    let build_term = |n| {
        if n < 2 { 
            panic!("n must be >= 2"); 
        }
        let mut sqrts = Vec::new();
        for i in 0..n { 
            sqrts.push(format!("(sqrt (var x{}))", i)); 
        }
        let last = sqrts[n-1].clone();
        let before_last = sqrts[n-2].clone();
        let mut t = format!("(add {} {})", before_last, last);
        for i in (0..n-2).rev() {
            let s = sqrts[i].clone();
            t = format!("(add {} {})", s, t);
        }
        format!("(neg (pow {} 2))", t)
    };
    let domain_pre = build_domain(3).clone();
    let domain = 
        domain_pre
            .iter()
            .map(|(s,d)| (s.as_str(), d.clone()))
            .collect::<Vec<_>>();
    convexify_check_expression_with_domain(domain, &build_term(3));
}