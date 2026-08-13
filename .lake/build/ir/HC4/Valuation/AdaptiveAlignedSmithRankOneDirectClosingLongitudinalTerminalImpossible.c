// Lean compiler output
// Module: HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalImpossible
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalStructure HC4.Newton.PositiveWeightTriangularEvaluation Mathlib.RingTheory.MvPolynomial.EulerIdentity Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___boxed(lean_object*);
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___lam__0___boxed), 1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Fin_cases___redArg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingLongitudinalTransverseWeight(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalStructure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_PositiveWeightTriangularEvaluation(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_RingTheory_MvPolynomial_EulerIdentity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalImpossible(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalStructure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_PositiveWeightTriangularEvaluation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_RingTheory_MvPolynomial_EulerIdentity(builtin, lean_io_mk_world());
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
