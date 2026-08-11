// Lean compiler output
// Module: HC4.Valuation.AdaptiveDegreeTwoKernelRestart
// Imports: Init HC4.Valuation.NonlinearDegreeBoundPreservation HC4.Valuation.CanonicalSmithDefectExposure HC4.Valuation.ExactKernelDefectDrop HC4.Valuation.ScaledDefect HC4.Valuation.AdaptiveGeometricRestartState HC4.Valuation.IntegralKernelSlopeExtraction HC4.Valuation.AdaptiveCoefficientOrder
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
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_nat_div(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_ScaleAwareAdaptiveGeometricRestartState_normalizedDefect(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_unsigned_to_nat(1u);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_6);
lean_ctor_set(x_9, 6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_AdaptiveGeometricRestartState_toScaleAware(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_NonlinearDegreeBoundPreservation(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_CanonicalSmithDefectExposure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_ExactKernelDefectDrop(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_ScaledDefect(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveGeometricRestartState(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_IntegralKernelSlopeExtraction(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveCoefficientOrder(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveDegreeTwoKernelRestart(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_NonlinearDegreeBoundPreservation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_CanonicalSmithDefectExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_ExactKernelDefectDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_ScaledDefect(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveGeometricRestartState(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_IntegralKernelSlopeExtraction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveCoefficientOrder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
