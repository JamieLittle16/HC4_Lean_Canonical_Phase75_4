// Lean compiler output
// Module: HC4.Polynomial.RankThreePencils
// Imports: Init HC4.Polynomial.MonomialHessian Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
LEAN_EXPORT lean_object* l_HC4_Polynomial_vectorHessianCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_sparseRankThreePencil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_vectorHessianCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_sparseRankThreePencil___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_oneZeroRankThreePencil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_oneZeroRankThreePencil___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Polynomial_vectorHessianCore___redArg___closed__0;
lean_object* l_Equiv_refl(lean_object*);
static lean_object* l_HC4_Polynomial_sparseRankThreePencil___redArg___closed__0;
LEAN_EXPORT lean_object* l_HC4_Polynomial_vectorHessianCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_vectorHessianCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_1, x_5);
lean_inc(x_6);
x_8 = lean_apply_1(x_1, x_6);
lean_inc(x_7);
x_9 = lean_apply_2(x_2, x_7, x_8);
x_10 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_11 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_3);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_2(x_4, x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec_ref(x_3);
x_14 = lean_apply_2(x_4, x_9, x_7);
return x_14;
}
}
}
static lean_object* _init_l_HC4_Polynomial_vectorHessianCore___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_refl(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_vectorHessianCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_1);
x_5 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_6 = l_AddGroupWithOne_toAddGroup___redArg(x_5);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_9 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_8);
lean_inc_ref(x_9);
x_10 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_HC4_Polynomial_vectorHessianCore___redArg___closed__0;
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_HC4_Polynomial_vectorHessianCore___redArg___lam__0), 6, 4);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_7);
x_15 = lean_apply_3(x_13, x_14, x_3, x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_vectorHessianCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Polynomial_vectorHessianCore___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_HC4_Polynomial_sparseRankThreePencil___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_sparseRankThreePencil___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_1);
x_9 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_10 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_9);
lean_inc_ref(x_10);
x_11 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc_ref(x_1);
x_16 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_17 = l_AddGroupWithOne_toAddGroup___redArg(x_16);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_HC4_Polynomial_vectorHessianCore___redArg___closed__0;
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_5);
x_26 = lean_apply_2(x_14, x_5, x_6);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_HC4_Polynomial_sparseRankThreePencil___redArg___closed__0;
lean_inc(x_12);
x_29 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, x_27);
lean_closure_set(x_29, 2, x_12);
lean_closure_set(x_29, 3, x_28);
lean_inc(x_26);
x_30 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_25);
lean_closure_set(x_30, 2, x_26);
lean_closure_set(x_30, 3, x_29);
lean_inc(x_12);
x_31 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_24);
lean_closure_set(x_31, 2, x_12);
lean_closure_set(x_31, 3, x_30);
lean_inc(x_12);
x_32 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, x_23);
lean_closure_set(x_32, 2, x_12);
lean_closure_set(x_32, 3, x_31);
lean_inc(x_20);
lean_inc(x_2);
x_33 = lean_apply_2(x_20, x_24, x_2);
lean_inc(x_19);
lean_inc(x_2);
x_34 = lean_apply_2(x_19, x_33, x_2);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_2);
x_35 = lean_apply_2(x_14, x_2, x_3);
lean_inc(x_14);
lean_inc(x_4);
x_36 = lean_apply_2(x_14, x_2, x_4);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, x_27);
lean_closure_set(x_37, 2, x_36);
lean_closure_set(x_37, 3, x_28);
lean_inc(x_35);
x_38 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_38, 0, lean_box(0));
lean_closure_set(x_38, 1, x_25);
lean_closure_set(x_38, 2, x_35);
lean_closure_set(x_38, 3, x_37);
x_39 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_39, 0, lean_box(0));
lean_closure_set(x_39, 1, x_24);
lean_closure_set(x_39, 2, x_34);
lean_closure_set(x_39, 3, x_38);
lean_inc(x_12);
x_40 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, x_23);
lean_closure_set(x_40, 2, x_12);
lean_closure_set(x_40, 3, x_39);
lean_inc(x_20);
lean_inc(x_3);
x_41 = lean_apply_2(x_20, x_24, x_3);
lean_inc(x_19);
lean_inc(x_3);
x_42 = lean_apply_2(x_19, x_41, x_3);
lean_inc(x_20);
lean_inc(x_5);
x_43 = lean_apply_2(x_20, x_24, x_5);
lean_inc(x_19);
x_44 = lean_apply_2(x_19, x_43, x_5);
lean_inc(x_14);
x_45 = lean_apply_2(x_14, x_6, x_44);
x_46 = lean_apply_2(x_15, x_42, x_45);
lean_inc(x_4);
x_47 = lean_apply_2(x_14, x_3, x_4);
lean_inc(x_47);
x_48 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_48, 0, lean_box(0));
lean_closure_set(x_48, 1, x_27);
lean_closure_set(x_48, 2, x_47);
lean_closure_set(x_48, 3, x_28);
x_49 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_49, 0, lean_box(0));
lean_closure_set(x_49, 1, x_25);
lean_closure_set(x_49, 2, x_46);
lean_closure_set(x_49, 3, x_48);
x_50 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_50, 0, lean_box(0));
lean_closure_set(x_50, 1, x_24);
lean_closure_set(x_50, 2, x_35);
lean_closure_set(x_50, 3, x_49);
x_51 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_51, 0, lean_box(0));
lean_closure_set(x_51, 1, x_23);
lean_closure_set(x_51, 2, x_26);
lean_closure_set(x_51, 3, x_50);
lean_inc(x_4);
x_52 = lean_apply_2(x_20, x_24, x_4);
x_53 = lean_apply_2(x_19, x_52, x_4);
x_54 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_54, 0, lean_box(0));
lean_closure_set(x_54, 1, x_27);
lean_closure_set(x_54, 2, x_53);
lean_closure_set(x_54, 3, x_28);
x_55 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_25);
lean_closure_set(x_55, 2, x_47);
lean_closure_set(x_55, 3, x_54);
x_56 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_56, 0, lean_box(0));
lean_closure_set(x_56, 1, x_24);
lean_closure_set(x_56, 2, x_36);
lean_closure_set(x_56, 3, x_55);
x_57 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_57, 0, lean_box(0));
lean_closure_set(x_57, 1, x_23);
lean_closure_set(x_57, 2, x_12);
lean_closure_set(x_57, 3, x_56);
x_58 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_58, 0, lean_box(0));
lean_closure_set(x_58, 1, x_27);
lean_closure_set(x_58, 2, x_57);
lean_closure_set(x_58, 3, x_28);
x_59 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_59, 0, lean_box(0));
lean_closure_set(x_59, 1, x_25);
lean_closure_set(x_59, 2, x_51);
lean_closure_set(x_59, 3, x_58);
x_60 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_60, 0, lean_box(0));
lean_closure_set(x_60, 1, x_24);
lean_closure_set(x_60, 2, x_40);
lean_closure_set(x_60, 3, x_59);
x_61 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_61, 0, lean_box(0));
lean_closure_set(x_61, 1, x_23);
lean_closure_set(x_61, 2, x_32);
lean_closure_set(x_61, 3, x_60);
x_62 = lean_apply_3(x_22, x_61, x_7, x_8);
return x_62;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_sparseRankThreePencil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_Polynomial_sparseRankThreePencil___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_oneZeroRankThreePencil___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_inc_ref(x_1);
x_9 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_10 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_9);
lean_inc_ref(x_10);
x_11 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc_ref(x_1);
x_16 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_17 = l_AddGroupWithOne_toAddGroup___redArg(x_16);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_HC4_Polynomial_vectorHessianCore___redArg___closed__0;
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_4);
x_26 = lean_apply_2(x_14, x_4, x_6);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_5);
x_28 = lean_apply_2(x_14, x_5, x_6);
x_29 = l_HC4_Polynomial_sparseRankThreePencil___redArg___closed__0;
lean_inc(x_28);
x_30 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_27);
lean_closure_set(x_30, 2, x_28);
lean_closure_set(x_30, 3, x_29);
lean_inc(x_26);
x_31 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_25);
lean_closure_set(x_31, 2, x_26);
lean_closure_set(x_31, 3, x_30);
lean_inc(x_12);
x_32 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, x_24);
lean_closure_set(x_32, 2, x_12);
lean_closure_set(x_32, 3, x_31);
lean_inc(x_12);
x_33 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, x_23);
lean_closure_set(x_33, 2, x_12);
lean_closure_set(x_33, 3, x_32);
lean_inc(x_3);
x_34 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, x_27);
lean_closure_set(x_34, 2, x_3);
lean_closure_set(x_34, 3, x_29);
lean_inc(x_2);
x_35 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_35, 0, lean_box(0));
lean_closure_set(x_35, 1, x_25);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_34);
lean_inc(x_12);
x_36 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_36, 0, lean_box(0));
lean_closure_set(x_36, 1, x_24);
lean_closure_set(x_36, 2, x_12);
lean_closure_set(x_36, 3, x_35);
x_37 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, x_23);
lean_closure_set(x_37, 2, x_12);
lean_closure_set(x_37, 3, x_36);
lean_inc(x_20);
lean_inc(x_2);
x_38 = lean_apply_2(x_20, x_24, x_2);
lean_inc(x_19);
lean_inc(x_2);
x_39 = lean_apply_2(x_19, x_38, x_2);
lean_inc(x_20);
lean_inc(x_4);
x_40 = lean_apply_2(x_20, x_24, x_4);
lean_inc(x_19);
lean_inc(x_4);
x_41 = lean_apply_2(x_19, x_40, x_4);
lean_inc(x_14);
lean_inc(x_6);
x_42 = lean_apply_2(x_14, x_6, x_41);
lean_inc(x_15);
x_43 = lean_apply_2(x_15, x_39, x_42);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_2);
x_44 = lean_apply_2(x_14, x_2, x_3);
lean_inc(x_14);
lean_inc(x_5);
x_45 = lean_apply_2(x_14, x_4, x_5);
lean_inc(x_14);
lean_inc(x_6);
x_46 = lean_apply_2(x_14, x_45, x_6);
lean_inc(x_15);
x_47 = lean_apply_2(x_15, x_44, x_46);
lean_inc(x_47);
x_48 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_48, 0, lean_box(0));
lean_closure_set(x_48, 1, x_27);
lean_closure_set(x_48, 2, x_47);
lean_closure_set(x_48, 3, x_29);
x_49 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_49, 0, lean_box(0));
lean_closure_set(x_49, 1, x_25);
lean_closure_set(x_49, 2, x_43);
lean_closure_set(x_49, 3, x_48);
x_50 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_50, 0, lean_box(0));
lean_closure_set(x_50, 1, x_24);
lean_closure_set(x_50, 2, x_2);
lean_closure_set(x_50, 3, x_49);
x_51 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_51, 0, lean_box(0));
lean_closure_set(x_51, 1, x_23);
lean_closure_set(x_51, 2, x_26);
lean_closure_set(x_51, 3, x_50);
lean_inc(x_20);
lean_inc(x_3);
x_52 = lean_apply_2(x_20, x_24, x_3);
lean_inc(x_19);
lean_inc(x_3);
x_53 = lean_apply_2(x_19, x_52, x_3);
lean_inc(x_5);
x_54 = lean_apply_2(x_20, x_24, x_5);
x_55 = lean_apply_2(x_19, x_54, x_5);
x_56 = lean_apply_2(x_14, x_6, x_55);
x_57 = lean_apply_2(x_15, x_53, x_56);
x_58 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_58, 0, lean_box(0));
lean_closure_set(x_58, 1, x_27);
lean_closure_set(x_58, 2, x_57);
lean_closure_set(x_58, 3, x_29);
x_59 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_59, 0, lean_box(0));
lean_closure_set(x_59, 1, x_25);
lean_closure_set(x_59, 2, x_47);
lean_closure_set(x_59, 3, x_58);
x_60 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_60, 0, lean_box(0));
lean_closure_set(x_60, 1, x_24);
lean_closure_set(x_60, 2, x_3);
lean_closure_set(x_60, 3, x_59);
x_61 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_61, 0, lean_box(0));
lean_closure_set(x_61, 1, x_23);
lean_closure_set(x_61, 2, x_28);
lean_closure_set(x_61, 3, x_60);
x_62 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_62, 0, lean_box(0));
lean_closure_set(x_62, 1, x_27);
lean_closure_set(x_62, 2, x_61);
lean_closure_set(x_62, 3, x_29);
x_63 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_63, 0, lean_box(0));
lean_closure_set(x_63, 1, x_25);
lean_closure_set(x_63, 2, x_51);
lean_closure_set(x_63, 3, x_62);
x_64 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_64, 0, lean_box(0));
lean_closure_set(x_64, 1, x_24);
lean_closure_set(x_64, 2, x_37);
lean_closure_set(x_64, 3, x_63);
x_65 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_65, 0, lean_box(0));
lean_closure_set(x_65, 1, x_23);
lean_closure_set(x_65, 2, x_33);
lean_closure_set(x_65, 3, x_64);
x_66 = lean_apply_3(x_22, x_65, x_7, x_8);
return x_66;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_oneZeroRankThreePencil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_Polynomial_oneZeroRankThreePencil___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_MonomialHessian(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial_RankThreePencils(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_MonomialHessian(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Polynomial_vectorHessianCore___redArg___closed__0 = _init_l_HC4_Polynomial_vectorHessianCore___redArg___closed__0();
lean_mark_persistent(l_HC4_Polynomial_vectorHessianCore___redArg___closed__0);
l_HC4_Polynomial_sparseRankThreePencil___redArg___closed__0 = _init_l_HC4_Polynomial_sparseRankThreePencil___redArg___closed__0();
lean_mark_persistent(l_HC4_Polynomial_sparseRankThreePencil___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
