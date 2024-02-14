/*!
Tests from the additional exercises in the Stanford Convex Optimization course:
https://github.com/cvxgrp/cvxbook_additional_exercises
!*/

use egg_pre_dcp::domain;
use egg_pre_dcp::test_util::{*};

// TODO: Failing because of qol curvature check simplification.
#[test]
fn test_3_32() {
    // 1 / (x * y) = (x^-0.5)^2 / y
    //             = qol(x^-0.5, y) (this is just one possibility)
    // pre_dcp_check_expression_with_domain(
    //     vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
    //     "(div 1 (mul (var x) (var y)))");
}

// TODO: Failing because of norm2 curvature check simplification.
#[test]
fn test_3_33() {
    // sqrt(1 + x^4 / y) = sqrt(1^2 + (x^2 / y)^2)
    //               ... = norm2(1, qol(x, y))
    // NOTE(RFM): Constant unfolding issue: x cannot be in the free domain as 
    // otherwise we cannot convert x^4 to (x^2)^2.
    // pre_dcp_check_expression_with_domain(
    //     vec![("x", domain::nonneg_dom()), ("y", domain::pos_dom())], 
    //     "(sqrt (add 1 (div (pow (var x) 4) (var y))))"
    // );
}

// TODO: Failing because of norm2 curvature check simplification.
#[test]
fn test_3_36_a() {
    // sqrt(1 + 4x^2 + 16y^2) = sqrt((2x)^2 + (sqrt(1^2 + (4y)^2))^2)
    //                    ... = norm2(2x, norm2(1, 4y))
    // pre_dcp_check_expression_with_domain(
    //     vec![("x", domain::nonneg_dom()), ("y", domain::nonneg_dom())], 
    //      "(sqrt (add 1 (add (mul 4 (pow (var x) 2)) (mul 16 (pow (var y) 2)))))");
}

#[test]
fn test_3_36_c() {
    // log(e^(2x + 3) + e^(4y + 5)) = lse(2x + 3, 4y + 5) 
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::free_dom()), ("y", domain::free_dom())], 
         "(log (add (exp (add (mul 2 (var x)) 3)) (exp (add (mul 4 (var y)) 5))))");
}

#[test]
fn test_3_38_e() {
    // (sqrt(x) + sqrt(y))^2 = x + y + 2sqrt(xy)
    //                   ... = x + y + 2geo(x, y)
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
         "(neg (pow (add (sqrt (var x)) (sqrt (var y))) 2))");
}

fn test_3_67_aux(n: usize, node_limit: usize) {
    // Generalizaiton of 3.28. Works for n = 3,4,5,6,7
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
    let domain_pre = build_domain(n).clone();
    let domain = 
        domain_pre
            .iter()
            .map(|(s,d)| (s.as_str(), d.clone()))
            .collect::<Vec<_>>();
        pre_dcp_check_expression_with_domain_and_node_limit(domain, &build_term(n), node_limit);
}

#[test]
fn test_3_67() {
    // for n in 2..11 {
    //     let now = Instant::now();
    //     {
    //         test_3_67_aux(n, 20000 * n);
    //     }
    //     let elapsed = now.elapsed();
    //     println!("Time for 3.67 (n={}): {:.2?}", n, elapsed);
    // }
    // node_limit = 20000 * n
    // n=2: 32359 nodes, 8 steps, 7.82s
    // n=3: 52870 nodes, 28 steps, 23.97s
    // n=4: 63224 nodes, 37 steps, 31.05s
    // n=5: 102470 nodes, 87 steps, 46.83s
    // n=6: 106484 nodes, 132 steps, 129.44s
    // n=7: 135393 nodes, 282 steps, 152.53s
    // n=8: 157549 nodes, 566 steps, 269.90s
    // n=9: 174177 nodes, 511 steps, 307.08s
    // n=10: 200372 nodes, 716 steps, 173.13s
}