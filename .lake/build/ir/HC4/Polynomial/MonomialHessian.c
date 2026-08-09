// Lean compiler output
// Module: HC4.Polynomial.MonomialHessian
// Imports: Init HC4.Polynomial.FourExponent HC4.Polynomial.HessianDeterminant Mathlib.LinearAlgebra.Matrix.SchurComplement Mathlib.Algebra.BigOperators.Fin
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
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* l_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_exponentHessianCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_exponentHessianCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_exponentHessianCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc_ref(x_1);
x_5 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_6 = l_AddGroupWithOne_toAddGroup___redArg(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_9 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_8);
lean_inc_ref(x_9);
x_10 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_9);
x_11 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
lean_inc(x_14);
lean_inc(x_3);
x_15 = lean_apply_1(x_14, x_3);
lean_inc(x_13);
x_16 = lean_apply_1(x_13, x_15);
lean_inc(x_4);
x_17 = lean_apply_1(x_14, x_4);
x_18 = lean_apply_1(x_13, x_17);
lean_inc(x_16);
x_19 = lean_apply_2(x_12, x_16, x_18);
x_20 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
x_21 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_apply_2(x_7, x_19, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_9);
x_24 = lean_apply_2(x_7, x_19, x_16);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_exponentHessianCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Polynomial_exponentHessianCore___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_FourExponent(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_HessianDeterminant(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Fin(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial_MonomialHessian(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_FourExponent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_HessianDeterminant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Fin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
