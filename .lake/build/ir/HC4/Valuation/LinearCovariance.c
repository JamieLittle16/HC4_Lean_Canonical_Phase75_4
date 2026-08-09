// Lean compiler output
// Module: HC4.Valuation.LinearCovariance
// Imports: Init HC4.Newton.TerminalCollision Mathlib.LinearAlgebra.Matrix.Determinant.Basic Mathlib.Data.Matrix.Action Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_linearGradientPullback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_linearGradientPullback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_DivInvOneMonoid_toInvOneClass___redArg(lean_object*);
lean_object* l_Matrix_mulVec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommGroupWithZero_toDivisionCommMonoid___redArg(lean_object*);
static lean_object* l_HC4_Valuation_hessianCongruence___redArg___closed__0;
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedLinearGradientPullback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_transpose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedHessianCongruence(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedLinearGradientPullback___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toSemifield___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedHessianCongruence___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Semifield_toCommGroupWithZero___redArg(lean_object*);
lean_object* l_List_finRange(lean_object*);
lean_object* l_Matrix_mulVec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Semiring_toNonAssocSemiring___redArg(lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Matrix_transpose___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_HC4_Valuation_hessianCongruence___redArg___lam__2), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = l_dotProduct___redArg(x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
static lean_object* _init_l_HC4_Valuation_hessianCongruence___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_List_finRange(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = l_Field_toEuclideanDomain___redArg(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_CommRing_toNonUnitalCommRing___redArg(x_7);
x_9 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_8);
lean_inc_ref(x_9);
x_10 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_9);
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_HC4_Valuation_hessianCongruence___redArg___lam__0), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_5);
x_14 = lean_alloc_closure((void*)(l_HC4_Valuation_hessianCongruence___redArg___lam__1), 3, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_4);
x_15 = l_HC4_Valuation_hessianCongruence___redArg___closed__0;
lean_inc_ref(x_12);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_HC4_Valuation_hessianCongruence___redArg___lam__3___boxed), 6, 5);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_11);
lean_closure_set(x_16, 3, x_12);
lean_closure_set(x_16, 4, x_14);
x_17 = l_dotProduct___redArg(x_15, x_11, x_12, x_16, x_13);
lean_dec_ref(x_12);
return x_17;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Valuation_hessianCongruence___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_hessianCongruence___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Valuation_hessianCongruence___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedHessianCongruence___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = l_Field_toSemifield___redArg(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = l_Semifield_toCommGroupWithZero___redArg(x_7);
x_10 = l_CommGroupWithZero_toDivisionCommMonoid___redArg(x_9);
x_11 = l_DivInvOneMonoid_toInvOneClass___redArg(x_10);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Semiring_toNonAssocSemiring___redArg(x_8);
lean_dec_ref(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_apply_1(x_12, x_2);
x_18 = l_HC4_Valuation_hessianCongruence___redArg(x_1, x_3, x_4, x_5, x_6);
x_19 = lean_apply_2(x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedHessianCongruence(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_Valuation_normalizedHessianCongruence___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_linearGradientPullback___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Field_toEuclideanDomain___redArg(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_CommRing_toNonUnitalCommRing___redArg(x_7);
x_9 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_8);
x_10 = l_HC4_Valuation_hessianCongruence___redArg___closed__0;
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Matrix_transpose), 6, 4);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, lean_box(0));
lean_closure_set(x_11, 3, x_2);
lean_inc_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_Matrix_mulVec), 8, 7);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, lean_box(0));
lean_closure_set(x_12, 3, x_9);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_2);
lean_closure_set(x_12, 6, x_4);
x_13 = lean_apply_1(x_3, x_12);
x_14 = l_Matrix_mulVec___redArg(x_9, x_10, x_11, x_13, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_linearGradientPullback(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Valuation_linearGradientPullback___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedLinearGradientPullback___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_7 = l_Field_toSemifield___redArg(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
x_9 = l_Semifield_toCommGroupWithZero___redArg(x_7);
x_10 = l_CommGroupWithZero_toDivisionCommMonoid___redArg(x_9);
x_11 = l_DivInvOneMonoid_toInvOneClass___redArg(x_10);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Field_toEuclideanDomain___redArg(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_CommRing_toNonUnitalCommRing___redArg(x_14);
x_16 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_15);
x_17 = l_Semiring_toNonAssocSemiring___redArg(x_8);
lean_dec_ref(x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_apply_1(x_12, x_2);
x_22 = l_HC4_Valuation_hessianCongruence___redArg___closed__0;
lean_inc(x_3);
x_23 = lean_alloc_closure((void*)(l_Matrix_transpose), 6, 4);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_3);
lean_inc_ref(x_16);
x_24 = lean_alloc_closure((void*)(l_Matrix_mulVec), 8, 7);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
lean_closure_set(x_24, 2, lean_box(0));
lean_closure_set(x_24, 3, x_16);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_3);
lean_closure_set(x_24, 6, x_5);
x_25 = lean_apply_1(x_4, x_24);
x_26 = l_Matrix_mulVec___redArg(x_16, x_22, x_23, x_25, x_6);
x_27 = lean_apply_2(x_20, x_21, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_normalizedLinearGradientPullback(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_Valuation_normalizedLinearGradientPullback___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalCollision(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Matrix_Action(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_LinearCovariance(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalCollision(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Matrix_Action(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_hessianCongruence___redArg___closed__0 = _init_l_HC4_Valuation_hessianCongruence___redArg___closed__0();
lean_mark_persistent(l_HC4_Valuation_hessianCongruence___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
