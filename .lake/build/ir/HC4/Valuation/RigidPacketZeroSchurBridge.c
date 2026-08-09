// Lean compiler output
// Module: HC4.Valuation.RigidPacketZeroSchurBridge
// Imports: Init HC4.Valuation.CanonicalSmithDefectExposure HC4.Valuation.SmithFrontierFourBlockExtraction HC4.Valuation.QuadraticFamilyCollision HC4.Newton.RigidPacketEvaluatedHessianChart HC4.Newton.ZeroSchurFirstEntryClock Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_rigidRightChartPerm___closed__1;
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidRightChartPerm;
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_rigidRightChartPerm___closed__0;
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_2);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Equiv_swapCore___at___Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_HC4_Valuation_rigidRightChartPerm___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rigidRightChartPerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_rigidRightChartPerm() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HC4_Valuation_rigidRightChartPerm___closed__0;
x_2 = l_HC4_Valuation_rigidRightChartPerm___closed__1;
x_3 = l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Equiv_swapCore___at___Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Equiv_swapCore___at___Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Equiv_swap___at___HC4_Valuation_rigidRightChartPerm_spec__0___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_CanonicalSmithDefectExposure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_SmithFrontierFourBlockExtraction(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_QuadraticFamilyCollision(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RigidPacketEvaluatedHessianChart(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_ZeroSchurFirstEntryClock(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_RigidPacketZeroSchurBridge(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_CanonicalSmithDefectExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_SmithFrontierFourBlockExtraction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_QuadraticFamilyCollision(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RigidPacketEvaluatedHessianChart(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_ZeroSchurFirstEntryClock(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_rigidRightChartPerm___closed__0 = _init_l_HC4_Valuation_rigidRightChartPerm___closed__0();
lean_mark_persistent(l_HC4_Valuation_rigidRightChartPerm___closed__0);
l_HC4_Valuation_rigidRightChartPerm___closed__1 = _init_l_HC4_Valuation_rigidRightChartPerm___closed__1();
lean_mark_persistent(l_HC4_Valuation_rigidRightChartPerm___closed__1);
l_HC4_Valuation_rigidRightChartPerm = _init_l_HC4_Valuation_rigidRightChartPerm();
lean_mark_persistent(l_HC4_Valuation_rigidRightChartPerm);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
