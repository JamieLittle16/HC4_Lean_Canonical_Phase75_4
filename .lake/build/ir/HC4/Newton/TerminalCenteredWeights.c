// Lean compiler output
// Module: HC4.Newton.TerminalCenteredWeights
// Imports: Init HC4.Newton.TerminalConformalFace Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_centeredTerminalWeight(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_centeredTerminalWeight___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_centeredTerminalWeight___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Newton_centeredTerminalWeight___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_centeredTerminalWeight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_HC4_Newton_centeredTerminalWeight___closed__0;
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_int_mul(x_4, x_5);
lean_dec(x_5);
x_7 = lean_int_sub(x_6, x_2);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_centeredTerminalWeight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_centeredTerminalWeight(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalConformalFace(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_TerminalCenteredWeights(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalConformalFace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_centeredTerminalWeight___closed__0 = _init_l_HC4_Newton_centeredTerminalWeight___closed__0();
lean_mark_persistent(l_HC4_Newton_centeredTerminalWeight___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
