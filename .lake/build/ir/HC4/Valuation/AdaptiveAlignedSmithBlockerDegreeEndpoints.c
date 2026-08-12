// Lean compiler output
// Module: HC4.Valuation.AdaptiveAlignedSmithBlockerDegreeEndpoints
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithCanonicalBlockerCompetition HC4.Newton.MixedDegreeWallRefinement Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithDegreePureBlockerEndpoint_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithDegreePureBlockerEndpoint_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithMixedDegreeBlockerEndpoint_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithMixedDegreeBlockerEndpoint_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithDegreePureBlockerEndpoint_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithDegreePureBlockerEndpoint_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_AdaptiveAlignedSmithDegreePureBlockerEndpoint_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithMixedDegreeBlockerEndpoint_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithMixedDegreeBlockerEndpoint_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_AdaptiveAlignedSmithMixedDegreeBlockerEndpoint_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithCanonicalBlockerCompetition(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_MixedDegreeWallRefinement(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithBlockerDegreeEndpoints(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithCanonicalBlockerCompetition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_MixedDegreeWallRefinement(builtin, lean_io_mk_world());
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
