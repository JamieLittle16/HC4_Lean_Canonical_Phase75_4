// Lean compiler output
// Module: HC4.Newton.RankTwoFourBlockSchur
// Imports: Init HC4.Newton.FirstSchurDeterminantOrder Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_determinantCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlockEntry_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurB___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurA(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurA___redArg(lean_object*, lean_object*);
lean_object* l_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* l_Field_toDivisionRing___redArg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlockEntry_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurBlock___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_determinantCore___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurC___redArg(lean_object*, lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_RankTwoFourBlock_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurA___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_1);
x_3 = l_Field_toDivisionRing___redArg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Ring_toAddGroupWithOne___redArg(x_4);
x_6 = l_AddGroupWithOne_toAddGroup___redArg(x_5);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Field_toEuclideanDomain___redArg(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_9);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 6);
lean_inc(x_18);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc(x_15);
lean_inc(x_14);
x_19 = lean_apply_2(x_13, x_14, x_15);
lean_inc(x_13);
x_20 = lean_apply_2(x_13, x_19, x_18);
lean_inc(x_13);
lean_inc(x_16);
x_21 = lean_apply_2(x_13, x_15, x_16);
lean_inc(x_13);
x_22 = lean_apply_2(x_13, x_21, x_16);
lean_inc(x_7);
x_23 = lean_apply_2(x_7, x_20, x_22);
lean_inc(x_13);
lean_inc(x_17);
x_24 = lean_apply_2(x_13, x_14, x_17);
x_25 = lean_apply_2(x_13, x_24, x_17);
x_26 = lean_apply_2(x_7, x_23, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurA(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_RankTwoFourBlock_schurA___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurB___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_1);
x_3 = l_Field_toDivisionRing___redArg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Ring_toAddGroupWithOne___redArg(x_4);
x_6 = l_AddGroupWithOne_toAddGroup___redArg(x_5);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Field_toEuclideanDomain___redArg(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_9);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 7);
lean_inc(x_20);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc(x_15);
lean_inc(x_14);
x_21 = lean_apply_2(x_13, x_14, x_15);
lean_inc(x_13);
x_22 = lean_apply_2(x_13, x_21, x_20);
lean_inc(x_13);
x_23 = lean_apply_2(x_13, x_15, x_16);
lean_inc(x_13);
x_24 = lean_apply_2(x_13, x_23, x_17);
lean_inc(x_7);
x_25 = lean_apply_2(x_7, x_22, x_24);
lean_inc(x_13);
x_26 = lean_apply_2(x_13, x_14, x_18);
x_27 = lean_apply_2(x_13, x_26, x_19);
x_28 = lean_apply_2(x_7, x_25, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurB(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_RankTwoFourBlock_schurB___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_1);
x_3 = l_Field_toDivisionRing___redArg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Ring_toAddGroupWithOne___redArg(x_4);
x_6 = l_AddGroupWithOne_toAddGroup___redArg(x_5);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Field_toEuclideanDomain___redArg(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = l_CommRing_toNonUnitalCommRing___redArg(x_9);
x_11 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_10);
x_12 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 8);
lean_inc(x_18);
lean_dec_ref(x_2);
lean_inc(x_13);
lean_inc(x_15);
lean_inc(x_14);
x_19 = lean_apply_2(x_13, x_14, x_15);
lean_inc(x_13);
x_20 = lean_apply_2(x_13, x_19, x_18);
lean_inc(x_13);
lean_inc(x_16);
x_21 = lean_apply_2(x_13, x_15, x_16);
lean_inc(x_13);
x_22 = lean_apply_2(x_13, x_21, x_16);
lean_inc(x_7);
x_23 = lean_apply_2(x_7, x_20, x_22);
lean_inc(x_13);
lean_inc(x_17);
x_24 = lean_apply_2(x_13, x_14, x_17);
x_25 = lean_apply_2(x_13, x_24, x_17);
x_26 = lean_apply_2(x_7, x_23, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_RankTwoFourBlock_schurC___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurBlock___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_3 = l_HC4_Newton_RankTwoFourBlock_schurA___redArg(x_1, x_2);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_4 = l_HC4_Newton_RankTwoFourBlock_schurB___redArg(x_1, x_2);
x_5 = l_HC4_Newton_RankTwoFourBlock_schurC___redArg(x_1, x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_schurBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_RankTwoFourBlock_schurBlock___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_determinantCore___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc_ref(x_1);
x_3 = l_Field_toEuclideanDomain___redArg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_CommRing_toNonUnitalCommRing___redArg(x_4);
x_6 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_5);
x_7 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Field_toDivisionRing___redArg(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = l_Ring_toAddGroupWithOne___redArg(x_11);
x_13 = l_AddGroupWithOne_toAddGroup___redArg(x_12);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 7);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 8);
lean_inc(x_24);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec_ref(x_14);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_16);
x_26 = lean_apply_2(x_8, x_16, x_17);
lean_inc(x_8);
lean_inc(x_22);
lean_inc(x_26);
x_27 = lean_apply_2(x_8, x_26, x_22);
lean_inc(x_8);
lean_inc(x_24);
x_28 = lean_apply_2(x_8, x_27, x_24);
lean_inc(x_8);
lean_inc(x_23);
x_29 = lean_apply_2(x_8, x_26, x_23);
lean_inc(x_8);
lean_inc(x_23);
x_30 = lean_apply_2(x_8, x_29, x_23);
lean_inc(x_15);
x_31 = lean_apply_2(x_15, x_28, x_30);
lean_inc(x_8);
lean_inc(x_20);
lean_inc(x_16);
x_32 = lean_apply_2(x_8, x_16, x_20);
lean_inc(x_8);
lean_inc(x_20);
x_33 = lean_apply_2(x_8, x_32, x_20);
lean_inc(x_8);
lean_inc(x_24);
x_34 = lean_apply_2(x_8, x_33, x_24);
lean_inc(x_15);
x_35 = lean_apply_2(x_15, x_31, x_34);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_apply_1(x_25, x_36);
lean_inc(x_8);
lean_inc(x_16);
lean_inc(x_37);
x_38 = lean_apply_2(x_8, x_37, x_16);
lean_inc(x_8);
lean_inc(x_20);
x_39 = lean_apply_2(x_8, x_38, x_20);
lean_inc(x_8);
lean_inc(x_21);
x_40 = lean_apply_2(x_8, x_39, x_21);
lean_inc(x_8);
lean_inc(x_23);
x_41 = lean_apply_2(x_8, x_40, x_23);
lean_inc(x_9);
x_42 = lean_apply_2(x_9, x_35, x_41);
lean_inc(x_8);
lean_inc(x_21);
x_43 = lean_apply_2(x_8, x_16, x_21);
lean_inc(x_8);
lean_inc(x_21);
x_44 = lean_apply_2(x_8, x_43, x_21);
lean_inc(x_8);
lean_inc(x_22);
x_45 = lean_apply_2(x_8, x_44, x_22);
lean_inc(x_15);
x_46 = lean_apply_2(x_15, x_42, x_45);
lean_inc(x_8);
lean_inc(x_18);
lean_inc(x_17);
x_47 = lean_apply_2(x_8, x_17, x_18);
lean_inc(x_8);
lean_inc(x_18);
x_48 = lean_apply_2(x_8, x_47, x_18);
lean_inc(x_8);
x_49 = lean_apply_2(x_8, x_48, x_24);
lean_inc(x_15);
x_50 = lean_apply_2(x_15, x_46, x_49);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_37);
x_51 = lean_apply_2(x_8, x_37, x_17);
lean_inc(x_8);
lean_inc(x_18);
x_52 = lean_apply_2(x_8, x_51, x_18);
lean_inc(x_8);
lean_inc(x_19);
x_53 = lean_apply_2(x_8, x_52, x_19);
lean_inc(x_8);
x_54 = lean_apply_2(x_8, x_53, x_23);
lean_inc(x_9);
x_55 = lean_apply_2(x_9, x_50, x_54);
lean_inc(x_8);
lean_inc(x_19);
x_56 = lean_apply_2(x_8, x_17, x_19);
lean_inc(x_8);
lean_inc(x_19);
x_57 = lean_apply_2(x_8, x_56, x_19);
lean_inc(x_8);
x_58 = lean_apply_2(x_8, x_57, x_22);
lean_inc(x_15);
x_59 = lean_apply_2(x_15, x_55, x_58);
lean_inc(x_8);
lean_inc_n(x_18, 2);
x_60 = lean_apply_2(x_8, x_18, x_18);
lean_inc(x_8);
lean_inc(x_21);
x_61 = lean_apply_2(x_8, x_60, x_21);
lean_inc(x_8);
lean_inc(x_21);
x_62 = lean_apply_2(x_8, x_61, x_21);
lean_inc(x_9);
x_63 = lean_apply_2(x_9, x_59, x_62);
lean_inc(x_8);
x_64 = lean_apply_2(x_8, x_37, x_18);
lean_inc(x_8);
lean_inc(x_19);
x_65 = lean_apply_2(x_8, x_64, x_19);
lean_inc(x_8);
lean_inc(x_20);
x_66 = lean_apply_2(x_8, x_65, x_20);
lean_inc(x_8);
x_67 = lean_apply_2(x_8, x_66, x_21);
x_68 = lean_apply_2(x_15, x_63, x_67);
lean_inc(x_8);
lean_inc(x_19);
x_69 = lean_apply_2(x_8, x_19, x_19);
lean_inc(x_8);
lean_inc(x_20);
x_70 = lean_apply_2(x_8, x_69, x_20);
x_71 = lean_apply_2(x_8, x_70, x_20);
x_72 = lean_apply_2(x_9, x_68, x_71);
return x_72;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlock_determinantCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_RankTwoFourBlock_determinantCore___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlockEntry_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankTwoFourBlockEntry_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_RankTwoFourBlockEntry_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FirstSchurDeterminantOrder(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_RankTwoFourBlockSchur(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FirstSchurDeterminantOrder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
