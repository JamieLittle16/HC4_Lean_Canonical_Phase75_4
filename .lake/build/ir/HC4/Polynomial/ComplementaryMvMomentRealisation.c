// Lean compiler output
// Module: HC4.Polynomial.ComplementaryMvMomentRealisation
// Imports: Init HC4.Polynomial.ComplementaryMvSubstitution Mathlib.LinearAlgebra.Matrix.Determinant.Basic Mathlib.Tactic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Polynomial_complementaryLineExponentValue___redArg___closed__0;
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_HC4_Polynomial_complementaryLineExponentValue___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_nat_mul(x_6, x_2);
x_12 = lean_nat_mul(x_11, x_9);
lean_dec(x_11);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_mul(x_6, x_3);
x_16 = lean_nat_mul(x_15, x_9);
lean_dec(x_15);
lean_inc(x_1);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_mul(x_7, x_4);
x_20 = lean_nat_sub(x_8, x_9);
x_21 = lean_nat_mul(x_19, x_20);
lean_dec(x_19);
lean_inc(x_1);
x_22 = lean_apply_1(x_1, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_mul(x_7, x_5);
x_25 = lean_nat_mul(x_24, x_20);
lean_dec(x_20);
lean_dec(x_24);
x_26 = lean_apply_1(x_1, x_25);
x_27 = l_HC4_Polynomial_complementaryLineExponentValue___redArg___closed__0;
x_28 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_23);
lean_closure_set(x_28, 2, x_26);
lean_closure_set(x_28, 3, x_27);
x_29 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, x_18);
lean_closure_set(x_29, 2, x_22);
lean_closure_set(x_29, 3, x_28);
x_30 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_14);
lean_closure_set(x_30, 2, x_17);
lean_closure_set(x_30, 3, x_29);
x_31 = l_Fin_cases___redArg(x_13, x_30, x_10);
lean_dec(x_13);
return x_31;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_HC4_Polynomial_complementaryLineExponentValue___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_Polynomial_complementaryLineExponentValue___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLineExponentValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_HC4_Polynomial_complementaryLineExponentValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryMvSubstitution(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial_ComplementaryMvMomentRealisation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryMvSubstitution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Polynomial_complementaryLineExponentValue___redArg___closed__0 = _init_l_HC4_Polynomial_complementaryLineExponentValue___redArg___closed__0();
lean_mark_persistent(l_HC4_Polynomial_complementaryLineExponentValue___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
