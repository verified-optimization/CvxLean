/*!
Tests adapted from random (non-DCP) problems generated by the DCP quiz:
https://dcp.stanford.edu/quiz
!*/

use egg_pre_dcp::domain;

use egg_pre_dcp::test_util::{*};

#[test]
fn test_quiz1() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::pos_dom())], 
        "(inv (inv (var x)))");
}

#[test]
fn test_quiz2() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
        "(neg (lse (log (var x)) (log (var y))))");
}

#[test]
fn test_quiz3() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::nonneg_dom())], 
        "(pow (sqrt (var x)) 2)");
}

#[test]
fn test_quiz4() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::nonneg_dom())], 
        "(neg (abs (sqrt (abs (var x)))))");
}

#[test]
fn test_quiz5() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::free_dom())], 
        "(div 1 (exp (var x)))");
}

#[test]
fn test_quiz6() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::nonneg_dom())], 
        "(neg (log (pow (mul 364 (var x)) 2)))");
}

#[test]
fn test_quiz7() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::pos_dom())], 
        "(pow (geo (add (var x) 2) (div 1 (var x))) 2)");
}

#[test]
fn test_quiz8() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::nonneg_dom())], 
        "(neg (log (abs (var x))))");
}

#[test]
fn test_quiz9() {
    pre_dcp_check_expression_with_domain(
        vec![("x", domain::pos_dom()), ("y", domain::pos_dom())], 
        "(div 1 (qol (inv (var x)) (inv (var y)))))");
}

#[test]
fn test_quiz10() {
    pre_dcp_check_expression(
        "(pow (log (exp (var x))) 2)");
}
