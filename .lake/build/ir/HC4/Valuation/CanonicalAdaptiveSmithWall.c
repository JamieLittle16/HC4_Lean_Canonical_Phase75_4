// Lean compiler output
// Module: HC4.Valuation.CanonicalAdaptiveSmithWall
// Imports: Init HC4.Valuation.AdaptiveDegreeTwoKernelRestart
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
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
static lean_object* _init_l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___lam__0___boxed), 1, 0);
x_5 = l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___closed__0;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight(lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight(lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_CanonicalAdaptiveSmithWallData_realization(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveDegreeTwoKernelRestart(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_CanonicalAdaptiveSmithWall(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveDegreeTwoKernelRestart(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___closed__0 = _init_l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___closed__0();
lean_mark_persistent(l_HC4_Valuation_constantZeroIntegralAdaptiveSmithWallWeight___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
