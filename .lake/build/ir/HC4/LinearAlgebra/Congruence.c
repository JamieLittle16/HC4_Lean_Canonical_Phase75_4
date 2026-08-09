// Lean compiler output
// Module: HC4.LinearAlgebra.Congruence
// Imports: Init Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_pullbackField___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_transpose___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_pullbackField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_dotProduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Matrix_transpose___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_congruence___redArg___lam__2), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = l_dotProduct___redArg(x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_8 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_7);
lean_inc_ref(x_8);
x_9 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_8);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_congruence___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_6);
x_13 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_congruence___redArg___lam__1), 3, 2);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_5);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_congruence___redArg___lam__3___boxed), 6, 5);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_13);
x_15 = l_dotProduct___redArg(x_2, x_10, x_11, x_14, x_12);
lean_dec_ref(x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_HC4_LinearAlgebra_congruence___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_congruence___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_LinearAlgebra_congruence___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_pullbackField___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_apply_1(x_4, x_6);
x_10 = lean_apply_1(x_5, x_9);
x_11 = l_HC4_LinearAlgebra_congruence___redArg(x_1, x_2, x_3, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_pullbackField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_HC4_LinearAlgebra_pullbackField___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_LinearAlgebra_Congruence(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
