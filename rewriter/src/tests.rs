#[cfg(test)]
mod tests {

use crate::domain;
use domain::Domain as Domain;

use crate::extract;
use extract::Minimization as Minimization;
use extract::get_steps as get_steps;
use extract::get_steps_from_string as get_steps_from_string; 

fn make(obj: &str, constrs: Vec<&str>) -> Minimization {
    let mut constrs_s = Vec::new();
    for i in 0..constrs.len() {
        let tag = format!("h{}", i);
        constrs_s.push((tag, constrs[i].to_string())); 
    }
    return Minimization {
        obj_fun : obj.to_string(),
        constrs : constrs_s,
    };
}

fn assert_steps_with_domain(domains : Vec<(&str, Domain)>, obj: &str, constrs: Vec<&str>) {
    let prob = make(obj, constrs);
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), d.clone())).collect();
    let steps = get_steps(prob, domains, true);
    println!("{:?}", steps);
    assert!(steps.is_some());
}

fn assert_steps(obj: &str, constrs: Vec<&str>) {
    assert_steps_with_domain(vec![], obj, constrs);
}

// Used to test single expressions outside the context of an optimization 
// problem.
fn assert_steps_from_string_with_domain(domains : Vec<(&str, Domain)>, s: &str) {
    let domains = 
        domains.iter().map(|(s, d)| ((*s).to_string(), d.clone())).collect();
    let steps = get_steps_from_string(s, domains, true);
    println!("{:?}", steps);
    assert!(steps.is_some());
}

#[allow(unused)]
fn assert_steps_from_string(s: &str) {
    assert_steps_from_string_with_domain(vec![], s);
}


// Examples.

#[test]
fn test_main_example() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())],
        "0", 
        vec![
            "(le (div 1 (sqrt (var x))) (exp (var x)))"
        ]);
    
}

#[test]
fn test_agp2() {
    assert_steps(
        "(exp (var x))", 
        vec![
            "(le (mul (exp (var x)) (exp (var y))) (neg (div 2691 500)))"
        ]);
    
}

#[test]
fn test_gp3() {
    assert_steps(
        "(exp (var x))",
        vec![
            "(le (sqrt (add (mul (exp (var x)) (exp (var x))) (exp (var y)))) 1)"
        ]);
}

#[test]
fn test_gp4() {
    assert_steps(
        "(div 1 (div (exp (var x)) (exp (var y))))",
        vec![
            "(le 2 (exp (var x)))",
            "(le (exp (var x)) 3)",
            "(le (add (pow (exp (var x)) 2) (div (mul 3 (exp (var y))) (exp (var z)))) (sqrt (exp (var x))))",
            "(eq (div (exp (var x)) (exp (var y))) (pow (exp (var z)) 2))"
        ]);
}

#[test]
fn test_gp6() {
    assert_steps_with_domain(
        vec![("Aflr", domain::pos_dom()), ("α", domain::pos_dom()), ("β", domain::pos_dom()), ("γ", domain::pos_dom()), ("δ", domain::pos_dom())],
        "(div 1 (mul (mul (exp (var h)) (exp (var w))) (exp (var d))))", 
        vec![
            "(le (mul 2 (add (mul (exp (var h)) (exp (var d))) (mul (exp (var w)) (exp (var d))))) (param Awall))",
            "(le (mul (exp (var w)) (exp (var d))) (param Aflr))",
            "(le (param α) (div (exp (var h)) (exp (var w))))",
            "(le (div (exp (var h)) (exp (var w))) (param β))",
            "(le (param γ) (div (exp (var d)) (exp (var w))))",
            "(le (div (exp (var d)) (exp (var w))) (param δ))"
        ]);
}


#[test]
fn test_dqcp() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())], 
        "(var x)", 
        vec![
            "(le (sqrt (div (var x) (add (var x) 1))) 1)"
        ]);
}

// Cost function.

#[test]
fn test_cost_function_number_of_variable_occurences() {
    assert_steps(
        "0",
        vec![
            "(le (var x) (sub 1 (var x)))"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_2() {
    assert_steps(
        "0",
        vec![
            "(le (add (mul 2 (var x)) (var x)) 0)"
        ]);
}

#[test]
fn test_cost_function_number_of_variable_occurences_3() {
    assert_steps(
        "0",
        vec![
            "(le (add (mul 2 (var x)) (mul 3 (var x))) 0)"
        ]);
}

// Rule-based tests.

#[test]
fn test_log_le_log() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())],
        "0", 
        vec![
            "(le (log (var x)) (log (var y)))"
        ]);
}

#[test]
fn test_sub_iff_add_le() {
    assert_steps(
        "0", 
        vec![
            "(le (add 1 (var x)) (var x))",
        ])
}

#[test]
fn test_log_le_log_rev() {
    assert_steps(
        "0", 
        vec![
            "(le (exp (var x)) (exp (var y)))"
        ]);
}

#[test]
fn test_exp_add() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())],
        "0",
        vec![
            "(le (exp (add (log (var x)) 2)) 1)"
        ]);
}

#[test]
fn test_exp_neg_eq_one_div_obj() {
    assert_steps_with_domain(
        vec![("x", Domain::make_ci(domain::one()))],
        "(mul (var x) (exp (neg (log (var x)))))",
        vec![
        ]);
}

#[test]
fn test_exp_neg_eq_one_div_constr() {
    assert_steps_with_domain(
        vec![("x", Domain::make_ci(domain::one()))],
        "(le (mul (var x) (exp (neg (log (var x))))) (var x))",
        vec![
        ]);
}

#[test]
fn test_log_mul_rev_constr() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())],
        "0",
        vec![
            "(le (exp (add (log (var x)) (log (add (var x) 1)))) 1)"
        ]);
}

#[test]
fn test_exp_neg_eq_one_div_rev() {
    assert_steps(
        "(div 1 (exp (var x)))",
        vec![
            "(le 1 (var x))"
        ]);
}

#[test]
fn test_div_self() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())], 
        "0", 
        vec![
            "(le (mul (div (var x) (var x)) (var y)) 1)"
        ]);
}

#[test]
fn test_div_le_iff_rev() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())], 
        "0", 
        vec![
            "(le (mul (var x) (var y)) (var x))"
        ]);
}

#[test]
fn test_log_div_rev_obj() {
    assert_steps_with_domain(
        vec![("x", domain::pos_dom())], 
        "(neg (sub (log (pow (var x) 2)) (log (var x))))", 
        vec![
        ]);
}

// Folding atoms. 

#[test]
fn test_geo_mean() {
    assert_steps_from_string_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
        "(neg (sqrt (mul (var x) (var y))))");
}

#[test]
fn test_quad_over_lin() {
    assert_steps_from_string_with_domain(
        vec![("x", domain::free_dom()), ("y", domain::pos_dom())], 
        "(div (pow (var x) 2) (var y))");
}

#[test]
fn test_norm2() {
    assert_steps_from_string_with_domain(
        vec![("x", domain::free_dom()), ("y", domain::free_dom())], 
        "(sqrt (add (pow (var x) 2) (pow (var y) 2)))");
}

// Misc.

#[test]
fn test_norm2_with_one() {
    assert_steps_from_string_with_domain(
        vec![("x", domain::free_dom())], 
        "(sqrt (add (pow (var x) 2) 1))");
}

#[test]
fn test_sqrt_pow4() {
    assert_steps_from_string_with_domain(
        vec![("x", domain::nonneg_dom())], 
        "(sqrt (pow (var x) 4))");
}

// From Stanford course, additional exercises. 

#[test]
fn test_3_32() {
    // 1 / (x * y) = (x^-0.5)^2 / y
    //             = qol(x^-0.5, y) (this is just one possibility)
    assert_steps_from_string_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
        "(div 1 (mul (var x) (var y)))");
}



#[test]
fn test_3_33() {
    // sqrt(1 + x^4 / y) = sqrt(1^2 + (x^2 / y)^2)
    //               ... = norm2(1, qol(x, y))
    // NOTE(RFM): Constant unfolding issue: x cannot be in the free domain as 
    // otherwise we cannot convert x^4 to (x^2)^2.
    assert_steps_from_string_with_domain(
        vec![("x", domain::nonneg_dom()), ("y", domain::pos_dom())], 
        "(sqrt (add 1 (div (pow (var x) 4) (var y))))"
    );
}

#[test]
fn test_3_36_a() {
    // sqrt(1 + 4x^2 + 16y^2) = sqrt((2x)^2 + (sqrt(1^2 + (4y)^2))^2)
    //                    ... = norm2(2x, norm2(1, 4y))
    assert_steps_from_string_with_domain(
        vec![("x", domain::nonneg_dom()), ("y", domain::nonneg_dom())], 
         "(sqrt (add 1 (add (mul 4 (pow (var x) 2)) (mul 16 (pow (var y) 2)))))");
}

#[test]
fn test_3_36_c() {
    // log(e^(2x + 3) + e^(4y + 5)) = lse(2x + 3, 4y + 5) 
    assert_steps_from_string_with_domain(
        vec![("x", domain::free_dom()), ("y", domain::free_dom())], 
         "(log (add (exp (add (mul 2 (var x)) 3)) (exp (add (mul 4 (var y)) 5))))");
}

#[test]
fn test_3_38_e() {
    // (sqrt(x) + sqrt(y))^2 = x + y + 2sqrt(xy)
    //                   ... = x + y + 2geo(x, y)
    assert_steps_from_string_with_domain(
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
    assert_steps_from_string_with_domain(domain, &build_term(3));
}

}
