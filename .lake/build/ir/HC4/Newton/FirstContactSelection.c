// Lean compiler output
// Module: HC4.Newton.FirstContactSelection
// Imports: Init HC4.Newton.ScaledContact Mathlib.Data.Finset.Max
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
lean_object* l_Nat_cast___at___Std_Internal_IO_Async_System_getCPUInfo_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_HC4_Newton_nonlinearOutsideSupport___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_contactSlope___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_contactSlope(lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_Polynomial_ordinaryDegree4(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_HC4_Newton_nonlinearOutsideSupport___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(3u);
lean_inc_ref(x_2);
x_4 = l_HC4_Polynomial_ordinaryDegree4(x_2);
x_5 = lean_nat_dec_le(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_apply_1(x_6, x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_HC4_Newton_nonlinearOutsideSupport___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Multiset_filter___redArg(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_nonlinearOutsideSupport___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HC4_Newton_nonlinearOutsideSupport___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_nonlinearOutsideSupport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_nonlinearOutsideSupport(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_contactSlope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_HC4_Polynomial_ordinaryDegree4(x_3);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_5);
x_7 = l_Nat_cast___at___Std_Internal_IO_Async_System_getCPUInfo_spec__0(x_6);
x_8 = lean_apply_1(x_4, x_2);
x_9 = l_Nat_cast___at___Std_Internal_IO_Async_System_getCPUInfo_spec__0(x_8);
x_10 = l_Rat_div(x_7, x_9);
lean_dec_ref(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_contactSlope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_contactSlope(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_ScaledContact(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Max(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_FirstContactSelection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_ScaledContact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Max(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
