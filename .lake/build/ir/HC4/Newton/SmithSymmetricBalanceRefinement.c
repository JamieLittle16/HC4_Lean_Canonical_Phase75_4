// Lean compiler output
// Module: HC4.Newton.SmithSymmetricBalanceRefinement
// Imports: Init HC4.Newton.SmithFirstWallGradeClassification Mathlib.Tactic
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
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithSymmetricBalancedSubface(lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_Newton_smithSeparatorDelta(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___closed__0;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_HC4_Newton_smithSymmetricBalancedSubface___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_HC4_Newton_smithSymmetricBalancedSubface___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc_ref(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_int_dec_eq(x_4, x_2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_HC4_Newton_smithSeparatorDelta(x_6, x_6, x_3);
lean_dec_ref(x_3);
x_8 = l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___closed__0;
x_9 = lean_int_dec_eq(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithSymmetricBalancedSubface(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
x_5 = l_Multiset_filter___redArg(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_HC4_Newton_smithSymmetricBalancedSubface___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_SmithFirstWallGradeClassification(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_SmithSymmetricBalanceRefinement(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_SmithFirstWallGradeClassification(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___closed__0 = _init_l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___closed__0();
lean_mark_persistent(l_HC4_Newton_smithSymmetricBalancedSubface___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
