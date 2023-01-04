#include <lean/lean.h>
#include <lean/lean_gmp.h>
#include "arb.h"

void mpz_init_set_fmpz(mpz_t x, const fmpz_t y) {
    if (COEFF_IS_MPZ(*y)) {
        mpz_init_set(x, y);
    } else {
        mpz_init_set_si(x, *y);
    }
}

// Rat -> Rat x Rat
lean_obj_res sqrt_bounds(lean_obj_arg x) 
{
    lean_object * n = lean_ctor_get(x, 0);
    lean_object * d = lean_ctor_get(x, 1);

    arb_t num, den;
    arb_init(num);
    arb_init(den);
    
    if (lean_is_scalar(n)) {
        arb_set_si(num, lean_scalar_to_int(n));
    } else if (lean_is_mpz(n)) {
        mpz_t num_m;
        mpz_init(num_m);
        lean_extract_mpz_value(n, num_m);
        fmpz_t num_fm;
        fmpz_init(num_fm);
        fmpz_set_mpz(num_fm, num_m);
        arb_set_fmpz(num, num_fm);
    } 

    int den_i = lean_scalar_to_int(d);
    arb_set_si(den, den_i);

    arb_t x_a;
    arb_init(x_a);
    arb_div(x_a, num, den, 10);
    
    arb_t sqrt_x_a;
    arb_init(sqrt_x_a);
    arb_sqrt(sqrt_x_a, x_a, 10);
    
    arf_t lower_f, upper_f;
    arf_init(lower_f);
    arf_init(upper_f);
    arb_get_interval_arf(lower_f, upper_f, sqrt_x_a, 10);

    fmpq_t lower_q, upper_q;
    fmpq_init(lower_q);
    fmpq_init(upper_q);
    arf_get_fmpq(lower_q, lower_f);
    arf_get_fmpq(upper_q, upper_f);

    mpz_t lower_num, lower_den, upper_num, upper_den;
    mpz_init_set_fmpz(lower_num, &lower_q->num);
    mpz_init_set_fmpz(lower_den, &lower_q->den);
    mpz_init_set_fmpz(upper_num, &upper_q->num);
    mpz_init_set_fmpz(upper_den, &upper_q->den);

    lean_object * lb_n = lean_alloc_mpz(lower_num);
    lean_object * lb_d = lean_alloc_mpz(lower_den);
    lean_object * ub_n = lean_alloc_mpz(upper_num);
    lean_object * ub_d = lean_alloc_mpz(upper_den);

    lean_object * lb = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(lb, 0, lb_n);
    lean_ctor_set(lb, 1, lb_d);

    lean_object * ub = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(ub, 0, ub_n);
    lean_ctor_set(ub, 1, ub_d);

    lean_object * res = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(res, 0, lb);
    lean_ctor_set(res, 1, ub);

    return res;
}
