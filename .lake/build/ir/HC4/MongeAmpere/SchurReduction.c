// Lean compiler output
// Module: HC4.MongeAmpere.SchurReduction
// Imports: Init Mathlib.LinearAlgebra.Matrix.SchurComplement
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
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__2), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = l_dotProduct___redArg(x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_1);
x_9 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_10 = l_AddGroupWithOne_toAddGroup___redArg(x_9);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_13 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_12);
lean_inc_ref(x_13);
x_14 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_8);
lean_inc(x_7);
x_18 = lean_alloc_closure((void*)(l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__1), 3, 2);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_7);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__3___boxed), 6, 5);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_15);
lean_closure_set(x_19, 3, x_16);
lean_closure_set(x_19, 4, x_18);
x_20 = lean_apply_2(x_5, x_7, x_8);
x_21 = l_dotProduct___redArg(x_2, x_15, x_16, x_19, x_17);
lean_dec_ref(x_16);
x_22 = lean_apply_2(x_11, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_HC4_MongeAmpere_schur_u2081_u2081___redArg(x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2081_u2081___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_HC4_MongeAmpere_schur_u2081_u2081(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_1);
x_9 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_10 = l_AddGroupWithOne_toAddGroup___redArg(x_9);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_13 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_12);
lean_inc_ref(x_13);
x_14 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_HC4_MongeAmpere_schur_u2082_u2082___redArg___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_8);
lean_inc(x_7);
x_18 = lean_alloc_closure((void*)(l_HC4_MongeAmpere_schur_u2082_u2082___redArg___lam__1), 3, 2);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_7);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_HC4_MongeAmpere_schur_u2081_u2081___redArg___lam__3___boxed), 6, 5);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_15);
lean_closure_set(x_19, 3, x_16);
lean_closure_set(x_19, 4, x_18);
x_20 = lean_apply_2(x_3, x_7, x_8);
x_21 = l_dotProduct___redArg(x_2, x_15, x_16, x_19, x_17);
lean_dec_ref(x_16);
x_22 = lean_apply_2(x_11, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_HC4_MongeAmpere_schur_u2082_u2082___redArg(x_4, x_5, x_7, x_8, x_9, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_HC4_MongeAmpere_schur_u2082_u2082___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_HC4_MongeAmpere_schur_u2082_u2082(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec_ref(x_6);
return x_14;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_MongeAmpere_SchurReduction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_SchurComplement(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
