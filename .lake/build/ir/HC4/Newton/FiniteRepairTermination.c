// Lean compiler output
// Module: HC4.Newton.FiniteRepairTermination
// Imports: Init HC4.Newton.RankOnePacketReentry Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_measure___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_rankDefect(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_rankDefect___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_measure(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_RepairState_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_rankDefect(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(3u);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_rankDefect___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_RepairState_rankDefect(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_measure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(3u);
x_4 = lean_nat_mul(x_3, x_2);
x_5 = l_HC4_Newton_RepairState_rankDefect(x_1);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RepairState_measure___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_RepairState_measure(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RankOnePacketReentry(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_FiniteRepairTermination(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RankOnePacketReentry(builtin, lean_io_mk_world());
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
