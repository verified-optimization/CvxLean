#include <lean/lean.h>
#include <lean/lean_gmp.h>
#include "arb.h"

// Set x to the value of y, handling mpz/si issues.
void mpz_init_set_fmpz(mpz_t x, const fmpz_t y) {
    if (COEFF_IS_MPZ(*y)) {
        mpz_init_set(x, COEFF_TO_PTR(*y));
    } else {
        mpz_init_set_si(x, *y);
    }
}

/* From Arb types to lean_object. */

// Returns an object of type Int with the value of x.
lean_object * lean_int_alloc_fmpz(fmpz_t x) {
    mpz_t res;
    mpz_init_set_fmpz(res, x);
    return lean_alloc_mpz(res);
}

// Returns an object of type Rat with the value of x.
lean_object * lean_rat_alloc_fmpq(fmpq_t x) {
    lean_object * num = lean_int_alloc_fmpz(&x->num);
    lean_object * den = lean_int_alloc_fmpz(&x->den);
    lean_object * res = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(res, 0, num);
    lean_ctor_set(res, 1, den);
    return res;
}

// Returns an object of type Ball with the value of x.
lean_object * lean_ball_alloc_arb(arb_t x) {
    fmpq_t mid_q;
    fmpq_init(mid_q);
    arf_get_fmpq(mid_q, &x->mid);
    fmpq_t rad_q;
    fmpq_init(rad_q);
    mag_get_fmpq(rad_q, &x->rad);
    lean_object * mid_o = lean_rat_alloc_fmpq(mid_q);
    lean_object * rad_o = lean_rat_alloc_fmpq(rad_q);
    lean_object * res = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(res, 0, mid_o);
    lean_ctor_set(res, 1, rad_o);
    return res;
}

/* From lean_object to Arb types. */

// Sets x to the value of o, which is an Int.
void fmpz_set_lean_int(fmpz_t x, lean_object * o) {
    if (lean_is_scalar(o)) {
        fmpz_set_si(x, lean_scalar_to_int(o));
    } else if (lean_is_mpz(o)) {
        mpz_t m;
        mpz_init(m);
        lean_extract_mpz_value(o, m);
        fmpz_set_mpz(x, m);
    }
}

// Sets x to the value of o, which is a Rat.
void fmpq_set_lean_rat(fmpq_t x, lean_object * o) {
    lean_object * num = lean_ctor_get(o, 0);
    lean_object * den = lean_ctor_get(o, 1);
    fmpz_t num_f, den_f;
    fmpz_init(num_f);
    fmpz_init(den_f);
    fmpz_set_lean_int(num_f, num);
    fmpz_set_lean_int(den_f, den);
    fmpq_set_fmpz_frac(x, num_f, den_f);
}

// Sets x to the value of o, which is a Ball.
void arb_set_lean_ball(arb_t x, lean_object * o, slong prec) {
    lean_object * mid = lean_ctor_get(o, 0);
    lean_object * rad = lean_ctor_get(o, 1);
    fmpq_t mid_q, rad_q;
    fmpq_init(mid_q);
    fmpq_init(rad_q);
    fmpq_set_lean_rat(mid_q, mid);
    fmpq_set_lean_rat(rad_q, rad);
    arf_set_fmpq(arb_midref(x), mid_q, prec, FMPR_RND_NEAR);
    arf_t rad_f;
    arf_init(rad_f);
    arf_set_fmpq(rad_f, rad_q, prec, FMPR_RND_UP);
    mag_init_set_arf(arb_radref(x), rad_f);
}

lean_obj_res ball_sqrt(uint32_t prec, lean_obj_arg ball) 
{
    arb_t x;
    arb_init(x);
    arb_set_lean_ball(x, ball, prec);
    arb_sqrt(x, x, prec);
    lean_obj_res res = lean_ball_alloc_arb(x);

    return res;
}
