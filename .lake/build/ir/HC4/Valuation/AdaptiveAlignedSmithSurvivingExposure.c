// Lean compiler output
// Module: HC4.Valuation.AdaptiveAlignedSmithSurvivingExposure
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithStateBridge HC4.Valuation.AdaptiveSmithWallExposure Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___closed__0;
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_instAddCancelCommMonoid;
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_HC4_Newton_HasIntegralAdaptiveSmithWallWeight_combinedSourceWeight___redArg(lean_object*, lean_object*);
lean_object* l_Finset_sum___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Valuation_AdaptiveSurvivingWallExposureData_ctorIdx(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_HC4_Newton_HasIntegralAdaptiveSmithWallWeight_combinedSourceWeight___redArg(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_List_finRange(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = l_Nat_instAddCancelCommMonoid;
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_alloc_closure((void*)(l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_nat_mul(x_6, x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___closed__0;
x_13 = l_Finset_sum___redArg(x_4, x_12, x_8);
x_14 = lean_nat_mul(x_10, x_13);
lean_dec(x_13);
x_15 = lean_nat_add(x_9, x_14);
lean_dec(x_14);
lean_dec(x_9);
x_16 = lean_nat_mul(x_11, x_5);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithStateBridge(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveSmithWallExposure(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithSurvivingExposure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithStateBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveSmithWallExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___closed__0 = _init_l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___closed__0();
lean_mark_persistent(l_HC4_Valuation_AdaptiveSurvivingWallExposureData_defect___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
