// Lean compiler output
// Module: HC4.Newton.AdaptivePacketExposure
// Imports: Init HC4.Newton.MixedDegreeWallRefinement Mathlib.Tactic
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
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__0(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__0___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* l_HC4_Newton_adaptivePacketExposureWeight___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_adaptivePacketExposureWeight___closed__1;
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__0(lean_object* x_1) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_HC4_Newton_adaptivePacketExposureWeight___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Newton_adaptivePacketExposureWeight___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_alloc_closure((void*)(l_HC4_Newton_adaptivePacketExposureWeight___lam__0___boxed), 1, 0);
x_4 = l_HC4_Newton_adaptivePacketExposureWeight___closed__0;
x_5 = lean_nat_to_int(x_1);
x_6 = lean_int_add(x_5, x_4);
x_7 = l_HC4_Newton_adaptivePacketExposureWeight___closed__1;
x_8 = lean_int_mul(x_7, x_5);
lean_dec(x_5);
x_9 = lean_int_add(x_8, x_4);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_HC4_Newton_adaptivePacketExposureWeight___lam__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_3);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_HC4_Newton_adaptivePacketExposureWeight___lam__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_HC4_Newton_adaptivePacketExposureWeight___lam__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Fin_cases___redArg(x_4, x_12, x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_adaptivePacketExposureWeight___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_adaptivePacketExposureWeight___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_adaptivePacketExposureWeight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_adaptivePacketExposureWeight(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_MixedDegreeWallRefinement(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_AdaptivePacketExposure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_MixedDegreeWallRefinement(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_adaptivePacketExposureWeight___closed__0 = _init_l_HC4_Newton_adaptivePacketExposureWeight___closed__0();
lean_mark_persistent(l_HC4_Newton_adaptivePacketExposureWeight___closed__0);
l_HC4_Newton_adaptivePacketExposureWeight___closed__1 = _init_l_HC4_Newton_adaptivePacketExposureWeight___closed__1();
lean_mark_persistent(l_HC4_Newton_adaptivePacketExposureWeight___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
