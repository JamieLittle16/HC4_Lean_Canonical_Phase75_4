// Lean compiler output
// Module: HC4.Valuation.RigidClosingFirstKernelStage
// Imports: Init HC4.Valuation.RigidClosingRecenteredSource HC4.Valuation.ExactKernelDefectDrop HC4.Valuation.GeometricAssemblyEntry HC4.Valuation.AlignedSmithWallArithmetic HC4.Valuation.ScaledDefect Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidClosingCommonKernel;
static lean_object* l_HC4_Valuation_rigidClosingCommonKernel___closed__0;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_rigidClosingCommonKernel___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rigidClosingCommonKernel() {
_start:
{
lean_object* x_1; 
x_1 = l_HC4_Valuation_rigidClosingCommonKernel___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_RigidClosingRecenteredSource(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_ExactKernelDefectDrop(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_GeometricAssemblyEntry(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AlignedSmithWallArithmetic(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_ScaledDefect(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_RigidClosingFirstKernelStage(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_RigidClosingRecenteredSource(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_ExactKernelDefectDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_GeometricAssemblyEntry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AlignedSmithWallArithmetic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_ScaledDefect(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_rigidClosingCommonKernel___closed__0 = _init_l_HC4_Valuation_rigidClosingCommonKernel___closed__0();
lean_mark_persistent(l_HC4_Valuation_rigidClosingCommonKernel___closed__0);
l_HC4_Valuation_rigidClosingCommonKernel = _init_l_HC4_Valuation_rigidClosingCommonKernel();
lean_mark_persistent(l_HC4_Valuation_rigidClosingCommonKernel);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
