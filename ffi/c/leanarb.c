#include <lean/lean.h>
#include "arb.h"

// Rat -> Rat x Rat
lean_obj_res sqrt_bounds(lean_obj_arg x) 
{
    lean_object * n = lean_ctor_get(x, 0);
    lean_object * d = lean_ctor_get(x, 1);

    arb_t num, den;
    arb_init(num);
    arb_init(den);
    
    // int num_i = lean_scalar_to_int(n);
    // arb_set_si(num, num_i);

    // int den_i = lean_scalar_to_int(d);
    // arb_set_si(den, den_i);

    // arb_t x_a;
    // arb_init(x_a);
    // arb_div(x_a, num, den, 10);
    
    // arb_t sqrt_x_a;
    // arb_init(sqrt_x_a);
    // arb_sqrt(sqrt_x_a, x_a, 10);
    
    // arf_t lower_f, upper_f;
    // arb_get_interval_arf(lower_f, upper_f, sqrt_x_a, 10);

    // fmpz_t lower_f, upper_f, one_f, exp_f;
    // fmpz_init(lower_f);
    // fmpz_init(upper_f);
    // fmpz_init(one_f);
    // fmpz_init(exp_f);
    // fmpz_one(one_f);
    // arb_get_interval_fmpz_2exp(lower_f, upper_f, exp_f, sqrt_x_a);
    // fmpz_mul_2exp(exp_f, one_f, *exp_f);

    // mpz_t lb_num, ub_num, b_den;
    // mpz_init(lb_num);
    // mpz_init(ub_num);
    // mpz_init(b_den);
    // fmpz_get_mpz(lb_num, lower_f);
    // fmpz_get_mpz(ub_num, upper_f);
    // fmpz_get_mpz(b_den, exp_f);

    lean_object * lb_n = n;//lean_alloc_mpz(lb_num);
    lean_object * ub_n = d;//lean_alloc_mpz(ub_num);
    lean_object * b_d = d;//lean_alloc_mpz(b_den);

    lean_object * lb = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(lb, 0, lb_n);
    lean_ctor_set(lb, 1, b_d);

    lean_object * ub = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(ub, 0, ub_n);
    lean_ctor_set(ub, 1, b_d);

    lean_object * res = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(res, 0, lb);
    lean_ctor_set(res, 1, ub);

    return res;
}
