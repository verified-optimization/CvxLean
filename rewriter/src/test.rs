
#[test]
fn test() {
    let s = "(le (div 1 (sqrt (var x))) (exp (var x)))".to_string();
    let s = "(add (var x) (var x))".to_string();
    // let s = "(prob 
    //     (objFun (add (add (mul (mul (div 1 (exp (var x))) (div 1 (sqrt (exp (var y))))) (div 1 (exp (var z)))) (mul (mul (div 23 10) (exp (var x))) (exp (var z)))) (mul (mul (mul 4 (exp (var x))) (exp (var y))) (exp (var z))))) 
    //     (constraints 
    //         (le (add (mul (mul (div 1 3) (div 1 (pow (exp (var x)) 2))) (div 1 (pow (exp (var y)) 2))) (mul (mul (div 4 3) (sqrt (exp (var y)))) (div 1 (exp (var z))))) 1) 
    //         (le (add (add (exp (var x)) (mul 2 (exp (var y)))) (mul 3 (exp (var z)))) 1) 
    //         (eq (mul (mul (div 1 2) (exp (var x))) (exp (var y))) 1)
    //     ))".to_string();
    let prob = Minimization {
        obj_fun : "(div 1 (div (exp (var x)) (exp (var y))))".to_string(),
        constrs : vec![
            ("h1".to_string(), "(le 2 (exp (var x)))".to_string()),
            ("h2".to_string(), "(le (exp (var x)) 3)".to_string()),
            ("h3".to_string(), "(le (add (pow (exp (var x)) 2) (div (mul 3 (exp (var y))) (exp (var z)))) (sqrt (exp (var x))))".to_string()),
            ("h4".to_string(), "(eq (div (exp (var x)) (exp (var y))) (pow (exp (var z)) 2))".to_string()),
        ]
    };
    let domains = vec![];
    let steps = get_steps(prob, domains, true);
    println!("{:?}", steps);
}
