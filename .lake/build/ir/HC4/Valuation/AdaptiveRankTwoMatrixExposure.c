// Lean compiler output
// Module: HC4.Valuation.AdaptiveRankTwoMatrixExposure
// Imports: Init HC4.Valuation.AdaptiveGeometricRestartState HC4.Valuation.AdaptiveRigidMatrixExposure HC4.Valuation.AdaptiveSmithWallExposure HC4.Newton.RigidPacketEvaluatedHessianChart HC4.Newton.RankTwoReesSchurEntry Mathlib.Tactic
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
static lean_object* l_HC4_Valuation_rankTwoAxisPerm___closed__5;
static lean_object* l_HC4_Valuation_rankTwoAxisPerm___closed__3;
static lean_object* l_HC4_Valuation_rankTwoAxisPerm___closed__0;
lean_object* l_Equiv_trans___redArg(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_rankTwoAxisPerm___closed__4;
lean_object* l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_rankTwoAxisPerm___closed__1;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_rankTwoAxisPerm;
static lean_object* l_HC4_Valuation_rankTwoAxisPerm___closed__2;
static lean_object* _init_l_HC4_Valuation_rankTwoAxisPerm___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rankTwoAxisPerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rankTwoAxisPerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HC4_Valuation_rankTwoAxisPerm___closed__1;
x_2 = l_HC4_Valuation_rankTwoAxisPerm___closed__0;
x_3 = l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rankTwoAxisPerm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rankTwoAxisPerm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HC4_Valuation_rankTwoAxisPerm___closed__0;
x_2 = l_HC4_Valuation_rankTwoAxisPerm___closed__3;
x_3 = l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rankTwoAxisPerm___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HC4_Valuation_rankTwoAxisPerm___closed__4;
x_2 = l_HC4_Valuation_rankTwoAxisPerm___closed__2;
x_3 = l_Equiv_trans___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rankTwoAxisPerm() {
_start:
{
lean_object* x_1; 
x_1 = l_HC4_Valuation_rankTwoAxisPerm___closed__5;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveGeometricRestartState(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveRigidMatrixExposure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveSmithWallExposure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RigidPacketEvaluatedHessianChart(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RankTwoReesSchurEntry(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveRankTwoMatrixExposure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveGeometricRestartState(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveRigidMatrixExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveSmithWallExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RigidPacketEvaluatedHessianChart(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RankTwoReesSchurEntry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_rankTwoAxisPerm___closed__0 = _init_l_HC4_Valuation_rankTwoAxisPerm___closed__0();
lean_mark_persistent(l_HC4_Valuation_rankTwoAxisPerm___closed__0);
l_HC4_Valuation_rankTwoAxisPerm___closed__1 = _init_l_HC4_Valuation_rankTwoAxisPerm___closed__1();
lean_mark_persistent(l_HC4_Valuation_rankTwoAxisPerm___closed__1);
l_HC4_Valuation_rankTwoAxisPerm___closed__2 = _init_l_HC4_Valuation_rankTwoAxisPerm___closed__2();
lean_mark_persistent(l_HC4_Valuation_rankTwoAxisPerm___closed__2);
l_HC4_Valuation_rankTwoAxisPerm___closed__3 = _init_l_HC4_Valuation_rankTwoAxisPerm___closed__3();
lean_mark_persistent(l_HC4_Valuation_rankTwoAxisPerm___closed__3);
l_HC4_Valuation_rankTwoAxisPerm___closed__4 = _init_l_HC4_Valuation_rankTwoAxisPerm___closed__4();
lean_mark_persistent(l_HC4_Valuation_rankTwoAxisPerm___closed__4);
l_HC4_Valuation_rankTwoAxisPerm___closed__5 = _init_l_HC4_Valuation_rankTwoAxisPerm___closed__5();
lean_mark_persistent(l_HC4_Valuation_rankTwoAxisPerm___closed__5);
l_HC4_Valuation_rankTwoAxisPerm = _init_l_HC4_Valuation_rankTwoAxisPerm();
lean_mark_persistent(l_HC4_Valuation_rankTwoAxisPerm);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
