// Lean compiler output
// Module: HC4.Valuation.AdaptiveAlignedSmithCanonicalBlockerCompetition
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalFirstWall Mathlib.Tactic
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
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_canonicalZeroSmithBase(lean_object*);
static lean_object* l_HC4_Valuation_canonicalZeroSmithBase___closed__0;
LEAN_EXPORT lean_object* l_HC4_Valuation_canonicalZeroSmithBase___boxed(lean_object*);
static lean_object* _init_l_HC4_Valuation_canonicalZeroSmithBase___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_canonicalZeroSmithBase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_canonicalZeroSmithBase___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_canonicalZeroSmithBase___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_canonicalZeroSmithBase(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithPureLongitudinalFirstWall(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithCanonicalBlockerCompetition(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithPureLongitudinalFirstWall(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_canonicalZeroSmithBase___closed__0 = _init_l_HC4_Valuation_canonicalZeroSmithBase___closed__0();
lean_mark_persistent(l_HC4_Valuation_canonicalZeroSmithBase___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
