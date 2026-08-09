// Lean compiler output
// Module: HC4.Polynomial.LogHessianMoments
// Imports: Init HC4.Polynomial.ComplementaryFractionBridge Mathlib.LinearAlgebra.Matrix.Determinant.Basic Mathlib.Tactic
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
lean_object* l_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_lineMomentHessian(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_DivisionRing_toDivInvMonoid___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* l_Field_toDivisionRing___redArg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_lineMomentHessian___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Polynomial_lineMomentHessian___redArg___closed__0;
LEAN_EXPORT lean_object* l_HC4_Polynomial_lineMomentHessian___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toSemifield___redArg(lean_object*);
static lean_object* l_HC4_Polynomial_complementaryLogBaseExponent___redArg___closed__0;
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Equiv_refl(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_lineMomentHessian___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_inc(x_6);
lean_inc(x_10);
x_24 = lean_apply_1(x_6, x_10);
lean_inc(x_11);
x_25 = lean_apply_1(x_6, x_11);
lean_inc(x_2);
lean_inc(x_25);
lean_inc(x_24);
x_26 = lean_apply_2(x_2, x_24, x_25);
x_27 = lean_nat_dec_eq(x_10, x_11);
if (x_27 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_inc_ref(x_9);
x_39 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_9);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_28 = x_40;
goto block_38;
}
else
{
lean_inc(x_24);
x_28 = x_24;
goto block_38;
}
block_23:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_apply_2(x_1, x_15, x_16);
lean_inc(x_2);
x_18 = lean_apply_2(x_2, x_3, x_17);
lean_inc(x_4);
x_19 = lean_apply_2(x_4, x_14, x_18);
lean_inc(x_2);
x_20 = lean_apply_2(x_2, x_12, x_13);
x_21 = lean_apply_2(x_2, x_5, x_20);
x_22 = lean_apply_2(x_4, x_19, x_21);
return x_22;
}
block_38:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_1);
x_29 = lean_apply_2(x_1, x_26, x_28);
lean_inc(x_2);
x_30 = lean_apply_2(x_2, x_7, x_29);
lean_inc(x_8);
x_31 = lean_apply_1(x_8, x_11);
lean_inc(x_2);
lean_inc(x_31);
x_32 = lean_apply_2(x_2, x_24, x_31);
x_33 = lean_apply_1(x_8, x_10);
lean_inc(x_2);
lean_inc(x_33);
x_34 = lean_apply_2(x_2, x_33, x_25);
lean_inc(x_4);
x_35 = lean_apply_2(x_4, x_32, x_34);
if (x_27 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_9);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_12 = x_33;
x_13 = x_31;
x_14 = x_30;
x_15 = x_35;
x_16 = x_37;
goto block_23;
}
else
{
lean_dec_ref(x_9);
lean_inc(x_33);
x_12 = x_33;
x_13 = x_31;
x_14 = x_30;
x_15 = x_35;
x_16 = x_33;
goto block_23;
}
}
}
}
static lean_object* _init_l_HC4_Polynomial_lineMomentHessian___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_refl(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_lineMomentHessian___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_1);
x_9 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_10 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_9);
lean_inc_ref(x_10);
x_11 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_15 = l_AddGroupWithOne_toAddGroup___redArg(x_14);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_HC4_Polynomial_lineMomentHessian___redArg___closed__0;
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_HC4_Polynomial_lineMomentHessian___redArg___lam__0), 11, 9);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_12);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_13);
lean_closure_set(x_19, 4, x_6);
lean_closure_set(x_19, 5, x_2);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_3);
lean_closure_set(x_19, 8, x_10);
x_20 = lean_apply_3(x_18, x_19, x_7, x_8);
return x_20;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_lineMomentHessian(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_Polynomial_lineMomentHessian___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_6);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_apply_2(x_3, x_4, x_8);
x_10 = lean_apply_2(x_5, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_1);
lean_inc(x_8);
x_10 = lean_apply_1(x_1, x_8);
lean_inc(x_9);
x_11 = lean_apply_1(x_1, x_9);
lean_inc(x_2);
lean_inc(x_10);
x_12 = lean_apply_2(x_2, x_10, x_11);
lean_inc(x_3);
lean_inc(x_8);
x_13 = lean_apply_1(x_3, x_8);
lean_inc(x_9);
x_14 = lean_apply_1(x_3, x_9);
lean_inc(x_2);
x_15 = lean_apply_2(x_2, x_13, x_14);
x_16 = lean_apply_2(x_2, x_4, x_15);
x_17 = lean_apply_2(x_5, x_12, x_16);
x_18 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_19 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_apply_2(x_7, x_17, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_6);
x_22 = lean_apply_2(x_7, x_17, x_10);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_1);
x_9 = l_Field_toDivisionRing___redArg(x_1);
lean_inc_ref(x_9);
x_10 = l_DivisionRing_toDivInvMonoid___redArg(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_9);
x_13 = l_Ring_toAddGroupWithOne___redArg(x_12);
x_14 = l_AddGroupWithOne_toAddGroup___redArg(x_13);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc_ref(x_1);
x_16 = l_Field_toEuclideanDomain___redArg(x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = l_CommRing_toNonUnitalCommRing___redArg(x_17);
x_19 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_18);
lean_inc_ref(x_19);
x_20 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Field_toSemifield___redArg(x_1);
lean_dec_ref(x_1);
x_24 = l_Semifield_toDivisionSemiring___redArg(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_HC4_Polynomial_lineMomentHessian___redArg___closed__0;
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_5);
x_29 = lean_apply_2(x_11, x_5, x_4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_3);
x_30 = lean_alloc_closure((void*)(l_HC4_Polynomial_logarithmicCoreFromMoments___redArg___lam__0), 6, 5);
lean_closure_set(x_30, 0, x_2);
lean_closure_set(x_30, 1, x_3);
lean_closure_set(x_30, 2, x_21);
lean_closure_set(x_30, 3, x_29);
lean_closure_set(x_30, 4, x_22);
lean_inc(x_21);
lean_inc(x_4);
x_31 = lean_apply_2(x_21, x_6, x_4);
x_32 = lean_unsigned_to_nat(2u);
lean_inc(x_26);
x_33 = lean_apply_2(x_26, x_32, x_5);
lean_inc(x_15);
x_34 = lean_apply_2(x_15, x_31, x_33);
x_35 = lean_apply_2(x_26, x_32, x_4);
x_36 = lean_apply_2(x_11, x_34, x_35);
x_37 = lean_alloc_closure((void*)(l_HC4_Polynomial_logarithmicCoreFromMoments___redArg___lam__1), 9, 7);
lean_closure_set(x_37, 0, x_30);
lean_closure_set(x_37, 1, x_21);
lean_closure_set(x_37, 2, x_3);
lean_closure_set(x_37, 3, x_36);
lean_closure_set(x_37, 4, x_22);
lean_closure_set(x_37, 5, x_19);
lean_closure_set(x_37, 6, x_15);
x_38 = lean_apply_3(x_28, x_37, x_7, x_8);
return x_38;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_logarithmicCoreFromMoments(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_Polynomial_logarithmicCoreFromMoments___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_HC4_Polynomial_complementaryLogBaseExponent___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_7 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_8 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_7);
lean_inc_ref(x_8);
x_9 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_15 = lean_apply_2(x_12, x_4, x_5);
lean_inc(x_12);
lean_inc(x_15);
x_16 = lean_apply_2(x_12, x_15, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_apply_2(x_12, x_15, x_3);
x_19 = l_HC4_Polynomial_complementaryLogBaseExponent___redArg___closed__0;
x_20 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
x_21 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, x_14);
lean_closure_set(x_21, 2, x_16);
lean_closure_set(x_21, 3, x_20);
lean_inc(x_10);
x_22 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_22, 0, lean_box(0));
lean_closure_set(x_22, 1, x_13);
lean_closure_set(x_22, 2, x_10);
lean_closure_set(x_22, 3, x_21);
x_23 = l_Fin_cases___redArg(x_10, x_22, x_6);
lean_dec(x_10);
return x_23;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_Polynomial_complementaryLogBaseExponent___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Polynomial_complementaryLogBaseExponent___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_complementaryLogBaseExponent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_Polynomial_complementaryLogBaseExponent(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryFractionBridge(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial_LogHessianMoments(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryFractionBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Polynomial_lineMomentHessian___redArg___closed__0 = _init_l_HC4_Polynomial_lineMomentHessian___redArg___closed__0();
lean_mark_persistent(l_HC4_Polynomial_lineMomentHessian___redArg___closed__0);
l_HC4_Polynomial_complementaryLogBaseExponent___redArg___closed__0 = _init_l_HC4_Polynomial_complementaryLogBaseExponent___redArg___closed__0();
lean_mark_persistent(l_HC4_Polynomial_complementaryLogBaseExponent___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
