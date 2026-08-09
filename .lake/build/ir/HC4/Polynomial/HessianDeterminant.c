// Lean compiler output
// Module: HC4.Polynomial.HessianDeterminant
// Imports: Init HC4.Polynomial.DeterminantWeight
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
extern lean_object* l_Int_instAddCommMonoid;
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_5, x_4);
lean_inc_ref(x_2);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_int_sub(x_3, x_7);
lean_dec(x_7);
x_9 = lean_apply_1(x_2, x_4);
x_10 = lean_int_sub(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_HC4_Polynomial_hessianTermWeight___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = l_Int_instAddCommMonoid;
x_7 = l_Finset_sum___redArg(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Polynomial_hessianTermWeight___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_hessianTermWeight___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Polynomial_hessianTermWeight___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_DeterminantWeight(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial_HessianDeterminant(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_DeterminantWeight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
