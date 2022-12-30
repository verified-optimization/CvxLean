#include <lean/lean.h>
#include <lean/lean_gmp.h>
#include "flint/flint.h"
#include "arb.h"

// Rat -> Rat x Rat
lean_obj_res sqrt_bounds(lean_obj_arg x) 
{
    lean_object * n = lean_ctor_get(x, 0);
    lean_object * d = lean_ctor_get(x, 1);

    mpz_t num, den;
    mpz_init(num);
    mpz_init(den);
    
    // if (lean_is_mpz(n)) {
    //     lean_extract_mpz_value(n, num);
    // } else {
        int num_i = 40;//lean_scalar_to_int(n);
        mpz_set_si(num, num_i);
    //}
    // if (lean_is_mpz(d)) {
    //     lean_extract_mpz_value(d, den);
    // } else {
        int den_i = 123;//lean_scalar_to_int(d);
        mpz_set_si(den, den_i);
    // }

    // fmpz_t x_f, num_f, den_f;
    // fmpz_init(x_f);
    // fmpz_init(num_f);
    // fmpz_init(den_f);
    // fmpz_set_mpz(num_f, num);
    // fmpz_set_mpz(den_f, den);
    // fmpz_divexact(x_f, num_f, den_f);

    arb_t x_a;
    // arb_init(x_a);
    // arb_set_fmpz(x_a, x_f);

    // arb_t sqrt_x_a;
    // arb_init(sqrt_x_a);
    // arb_sqrt(sqrt_x_a, x_a, 10);

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
