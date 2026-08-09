// Lean compiler output
// Module: HC4.Valuation.GeometricAssemblyEntry
// Imports: Init HC4.Valuation.CoupledSmithWallClosure HC4.Valuation.IntegralKernelSlopeExtraction Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_CanonicalGeometricRestartState_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___redArg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_CanonicalGeometricRestartState_toGlobal(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_CoupledSmithWallClosure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_IntegralKernelSlopeExtraction(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_GeometricAssemblyEntry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_CoupledSmithWallClosure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_IntegralKernelSlopeExtraction(builtin, lean_io_mk_world());
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
