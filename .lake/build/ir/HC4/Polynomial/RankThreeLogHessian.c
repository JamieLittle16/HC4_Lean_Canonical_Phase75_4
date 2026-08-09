// Lean compiler output
// Module: HC4.Polynomial.RankThreeLogHessian
// Imports: Init HC4.Polynomial.LogHessianMoments Mathlib.LinearAlgebra.Matrix.Determinant.Basic Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeWeightedCofactorSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_LieRing_ofAssociativeRing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___closed__0;
lean_object* l_AddGroupWithOne_toAddGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogProduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaNumerator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaDenominator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogSum___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeDirectionDefect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeDirectionDefect___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Polynomial_rankThreeLogHessianCore___redArg___closed__0;
lean_object* l_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeWeightedCofactorSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogSum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaDenominator___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaNumerator___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___closed__0;
x_10 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_11);
x_13 = l_Fin_cases___redArg(x_1, x_12, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Polynomial_rankThreeLogBaseExponent___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Polynomial_rankThreeLogBaseExponent___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogBaseExponent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Polynomial_rankThreeLogBaseExponent(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_closure((void*)(l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__0___boxed), 1, 0);
x_7 = lean_alloc_closure((void*)(l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__3___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Fin_cases___redArg(x_1, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Polynomial_rankThreeLogDirection___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Polynomial_rankThreeLogDirection___redArg___lam__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Polynomial_rankThreeLogDirection___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogDirection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Polynomial_rankThreeLogDirection(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_12 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_11);
x_13 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc(x_14);
lean_inc(x_9);
x_16 = lean_apply_2(x_14, x_9, x_5);
x_17 = lean_unsigned_to_nat(2u);
lean_inc(x_14);
lean_inc(x_9);
x_18 = lean_apply_2(x_14, x_9, x_6);
lean_inc(x_15);
x_19 = lean_apply_2(x_15, x_2, x_18);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
lean_inc(x_9);
x_21 = lean_apply_2(x_14, x_9, x_7);
lean_inc(x_15);
x_22 = lean_apply_2(x_15, x_3, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_apply_2(x_14, x_9, x_8);
x_25 = lean_apply_2(x_15, x_4, x_24);
x_26 = l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___closed__0;
x_27 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_23);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_26);
x_28 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_20);
lean_closure_set(x_28, 2, x_22);
lean_closure_set(x_28, 3, x_27);
x_29 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, x_17);
lean_closure_set(x_29, 2, x_19);
lean_closure_set(x_29, 3, x_28);
x_30 = l_Fin_cases___redArg(x_16, x_29, x_10);
lean_dec(x_16);
return x_30;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_HC4_Polynomial_rankThreeLogExponent___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_Polynomial_rankThreeLogExponent___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogExponent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_HC4_Polynomial_rankThreeLogExponent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_17 = l_HC4_Polynomial_rankThreeLogExponent___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_HC4_Polynomial_rankThreeLogExponent___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_inc(x_10);
lean_inc(x_17);
x_19 = lean_apply_2(x_10, x_17, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_HC4_Polynomial_rankThreeLogDirection___redArg(x_5, x_6, x_7, x_8, x_15);
x_21 = l_HC4_Polynomial_rankThreeLogDirection___redArg(x_5, x_6, x_7, x_8, x_16);
lean_dec(x_5);
lean_inc(x_10);
x_22 = lean_apply_2(x_10, x_20, x_21);
x_23 = lean_apply_2(x_10, x_11, x_22);
x_24 = lean_apply_2(x_12, x_19, x_23);
x_25 = lean_nat_dec_eq(x_15, x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
x_26 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_13);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_apply_2(x_14, x_24, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec_ref(x_13);
x_29 = lean_apply_2(x_14, x_24, x_17);
return x_29;
}
}
}
static lean_object* _init_l_HC4_Polynomial_rankThreeLogHessianCore___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_refl(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc_ref(x_1);
x_13 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_14 = l_AddGroupWithOne_toAddGroup___redArg(x_13);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc_ref(x_1);
x_16 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_17 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_16);
lean_inc_ref(x_17);
x_18 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_HC4_Polynomial_rankThreeLogHessianCore___redArg___closed__0;
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_HC4_Polynomial_rankThreeLogHessianCore___redArg___lam__0___boxed), 16, 14);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_7);
lean_closure_set(x_23, 7, x_8);
lean_closure_set(x_23, 8, x_9);
lean_closure_set(x_23, 9, x_19);
lean_closure_set(x_23, 10, x_10);
lean_closure_set(x_23, 11, x_20);
lean_closure_set(x_23, 12, x_17);
lean_closure_set(x_23, 13, x_15);
x_24 = lean_apply_3(x_22, x_23, x_11, x_12);
return x_24;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_HC4_Polynomial_rankThreeLogHessianCore___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogHessianCore___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_HC4_Polynomial_rankThreeLogHessianCore___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogProduct___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_13);
lean_inc(x_9);
x_15 = lean_apply_2(x_13, x_9, x_5);
lean_inc(x_13);
lean_inc(x_9);
x_16 = lean_apply_2(x_13, x_9, x_6);
lean_inc(x_14);
x_17 = lean_apply_2(x_14, x_2, x_16);
lean_inc(x_13);
x_18 = lean_apply_2(x_13, x_15, x_17);
lean_inc(x_13);
lean_inc(x_9);
x_19 = lean_apply_2(x_13, x_9, x_7);
lean_inc(x_14);
x_20 = lean_apply_2(x_14, x_3, x_19);
lean_inc(x_13);
x_21 = lean_apply_2(x_13, x_18, x_20);
lean_inc(x_13);
x_22 = lean_apply_2(x_13, x_9, x_8);
x_23 = lean_apply_2(x_14, x_4, x_22);
x_24 = lean_apply_2(x_13, x_21, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogProduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_Polynomial_rankThreeLogProduct___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogSum___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_13);
lean_inc(x_9);
x_15 = lean_apply_2(x_13, x_9, x_5);
lean_inc(x_13);
lean_inc(x_9);
x_16 = lean_apply_2(x_13, x_9, x_6);
lean_inc(x_14);
x_17 = lean_apply_2(x_14, x_2, x_16);
lean_inc(x_14);
x_18 = lean_apply_2(x_14, x_15, x_17);
lean_inc(x_13);
lean_inc(x_9);
x_19 = lean_apply_2(x_13, x_9, x_7);
lean_inc(x_14);
x_20 = lean_apply_2(x_14, x_3, x_19);
lean_inc(x_14);
x_21 = lean_apply_2(x_14, x_18, x_20);
x_22 = lean_apply_2(x_13, x_9, x_8);
lean_inc(x_14);
x_23 = lean_apply_2(x_14, x_4, x_22);
x_24 = lean_apply_2(x_14, x_21, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeLogSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_Polynomial_rankThreeLogSum___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeDirectionDefect___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_1);
x_6 = l_LieRing_ofAssociativeRing___redArg(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_SubNegZeroMonoid_toNegZeroClass___redArg(x_7);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_13);
x_14 = lean_apply_2(x_13, x_2, x_3);
lean_inc(x_13);
x_15 = lean_apply_2(x_13, x_14, x_4);
x_16 = lean_apply_2(x_13, x_15, x_5);
x_17 = lean_apply_1(x_9, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeDirectionDefect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Polynomial_rankThreeDirectionDefect___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeWeightedCofactorSum___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc_ref(x_1);
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = lean_unsigned_to_nat(2u);
lean_inc(x_16);
lean_inc(x_5);
x_18 = lean_apply_2(x_16, x_17, x_5);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_9);
x_19 = lean_apply_2(x_14, x_9, x_6);
lean_inc(x_15);
x_20 = lean_apply_2(x_15, x_2, x_19);
lean_inc(x_14);
lean_inc(x_20);
x_21 = lean_apply_2(x_14, x_18, x_20);
lean_inc(x_14);
lean_inc(x_7);
lean_inc(x_9);
x_22 = lean_apply_2(x_14, x_9, x_7);
lean_inc(x_15);
x_23 = lean_apply_2(x_15, x_3, x_22);
lean_inc(x_14);
lean_inc(x_23);
x_24 = lean_apply_2(x_14, x_21, x_23);
lean_inc(x_14);
lean_inc(x_8);
lean_inc(x_9);
x_25 = lean_apply_2(x_14, x_9, x_8);
lean_inc(x_15);
x_26 = lean_apply_2(x_15, x_4, x_25);
lean_inc(x_14);
lean_inc(x_26);
x_27 = lean_apply_2(x_14, x_24, x_26);
lean_inc(x_16);
x_28 = lean_apply_2(x_16, x_17, x_6);
lean_inc(x_14);
x_29 = lean_apply_2(x_14, x_9, x_5);
lean_inc(x_14);
lean_inc(x_29);
x_30 = lean_apply_2(x_14, x_28, x_29);
lean_inc(x_14);
lean_inc(x_23);
x_31 = lean_apply_2(x_14, x_30, x_23);
lean_inc(x_14);
lean_inc(x_26);
x_32 = lean_apply_2(x_14, x_31, x_26);
lean_inc(x_15);
x_33 = lean_apply_2(x_15, x_27, x_32);
lean_inc(x_16);
x_34 = lean_apply_2(x_16, x_17, x_7);
lean_inc(x_14);
lean_inc(x_29);
x_35 = lean_apply_2(x_14, x_34, x_29);
lean_inc(x_14);
lean_inc(x_20);
x_36 = lean_apply_2(x_14, x_35, x_20);
lean_inc(x_14);
x_37 = lean_apply_2(x_14, x_36, x_26);
lean_inc(x_15);
x_38 = lean_apply_2(x_15, x_33, x_37);
x_39 = lean_apply_2(x_16, x_17, x_8);
lean_inc(x_14);
x_40 = lean_apply_2(x_14, x_39, x_29);
lean_inc(x_14);
x_41 = lean_apply_2(x_14, x_40, x_20);
x_42 = lean_apply_2(x_14, x_41, x_23);
x_43 = lean_apply_2(x_15, x_38, x_42);
return x_43;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeWeightedCofactorSum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_Polynomial_rankThreeWeightedCofactorSum___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaNumerator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_1);
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc_ref(x_1);
x_14 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_15 = l_AddGroupWithOne_toAddGroup___redArg(x_14);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec_ref(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_19 = l_HC4_Polynomial_rankThreeLogProduct___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_20 = l_HC4_Polynomial_rankThreeLogSum___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_21 = lean_apply_2(x_17, x_18, x_20);
x_22 = lean_apply_2(x_13, x_19, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaNumerator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_Polynomial_rankThreeEtaNumerator___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaDenominator___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_1);
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc_ref(x_1);
x_15 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_16 = l_AddGroupWithOne_toAddGroup___redArg(x_15);
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = lean_ctor_get(x_18, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_22 = l_HC4_Polynomial_rankThreeLogSum___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_23 = lean_apply_2(x_19, x_20, x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_24 = l_HC4_Polynomial_rankThreeWeightedCofactorSum___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_inc(x_13);
x_25 = lean_apply_2(x_13, x_23, x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_1);
x_26 = l_HC4_Polynomial_rankThreeDirectionDefect___redArg(x_1, x_5, x_6, x_7, x_8);
x_27 = lean_unsigned_to_nat(2u);
lean_inc(x_21);
x_28 = lean_apply_2(x_21, x_27, x_26);
x_29 = l_HC4_Polynomial_rankThreeLogProduct___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_30 = lean_apply_2(x_13, x_28, x_29);
x_31 = lean_apply_2(x_14, x_25, x_30);
return x_31;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_rankThreeEtaDenominator(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_Polynomial_rankThreeEtaDenominator___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_LogHessianMoments(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial_RankThreeLogHessian(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_LogHessianMoments(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___closed__0 = _init_l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___closed__0();
lean_mark_persistent(l_HC4_Polynomial_rankThreeLogBaseExponent___redArg___closed__0);
l_HC4_Polynomial_rankThreeLogHessianCore___redArg___closed__0 = _init_l_HC4_Polynomial_rankThreeLogHessianCore___redArg___closed__0();
lean_mark_persistent(l_HC4_Polynomial_rankThreeLogHessianCore___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
