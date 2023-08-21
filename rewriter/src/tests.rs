#[cfg(test)]
mod tests {

use crate::extract;
use extract::Minimization as Minimization;
use extract::get_steps as get_steps;

fn make_basic(obj: &str, constrs: Vec<&str>) -> Minimization {
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

fn print_steps_basic(obj: &str, constrs: Vec<&str>) {
    let prob = make_basic(obj, constrs);
    let domains = vec![];
    let steps = get_steps(prob, domains, true);
    println!("{:?}", steps);
}

#[test]
fn test_simple_example() {
    print_steps_basic(
        "0", 
        vec![
            "(le (div 1 (sqrt (var x))) (exp (var x)))"
        ]);
}

#[test]
fn test_gp4() {
    print_steps_basic(
        "(div 1 (div (exp (var x)) (exp (var y))))",
        vec![
            "(le 2 (exp (var x)))",
            "(le (exp (var x)) 3)",
            "(le (add (pow (exp (var x)) 2) (div (mul 3 (exp (var y))) (exp (var z)))) (sqrt (exp (var x))))",
            "(eq (div (exp (var x)) (exp (var y))) (pow (exp (var z)) 2))"
        ]);
}

// let s = "(add (var x) (var x))".to_string();
// let s = "(prob 
//     (objFun (add (add (mul (mul (div 1 (exp (var x))) (div 1 (sqrt (exp (var y))))) (div 1 (exp (var z)))) (mul (mul (div 23 10) (exp (var x))) (exp (var z)))) (mul (mul (mul 4 (exp (var x))) (exp (var y))) (exp (var z))))) 
//     (constraints 
//         (le (add (mul (mul (div 1 3) (div 1 (pow (exp (var x)) 2))) (div 1 (pow (exp (var y)) 2))) (mul (mul (div 4 3) (sqrt (exp (var y)))) (div 1 (exp (var z))))) 1) 
//         (le (add (add (exp (var x)) (mul 2 (exp (var y)))) (mul 3 (exp (var z)))) 1) 
//         (eq (mul (mul (div 1 2) (exp (var x))) (exp (var y))) 1)
//     ))".to_string();
}
