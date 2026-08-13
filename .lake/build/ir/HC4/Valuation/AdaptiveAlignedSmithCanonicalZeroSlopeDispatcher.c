// Lean compiler output
// Module: HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroSlopeDispatcher
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithCanonicalJC2FreeDispatcher HC4.Valuation.AdaptivePositiveKernelFixedScaleProgress Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_adaptiveCanonicalCommonKernel;
static lean_object* l_HC4_Valuation_adaptiveCanonicalCommonKernel___closed__0;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_adaptiveCanonicalCommonKernel___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_adaptiveCanonicalCommonKernel() {
_start:
{
lean_object* x_1; 
x_1 = l_HC4_Valuation_adaptiveCanonicalCommonKernel___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithCanonicalJC2FreeDispatcher(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptivePositiveKernelFixedScaleProgress(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithCanonicalZeroSlopeDispatcher(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithCanonicalJC2FreeDispatcher(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptivePositiveKernelFixedScaleProgress(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_adaptiveCanonicalCommonKernel___closed__0 = _init_l_HC4_Valuation_adaptiveCanonicalCommonKernel___closed__0();
lean_mark_persistent(l_HC4_Valuation_adaptiveCanonicalCommonKernel___closed__0);
l_HC4_Valuation_adaptiveCanonicalCommonKernel = _init_l_HC4_Valuation_adaptiveCanonicalCommonKernel();
lean_mark_persistent(l_HC4_Valuation_adaptiveCanonicalCommonKernel);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
