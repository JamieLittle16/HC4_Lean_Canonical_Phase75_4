// Lean compiler output
// Module: HC4.Newton.FiniteValuationTilt
// Imports: Init HC4.Newton.SmithExtremeBalance Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltedValue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltedValue___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_finiteTiltEpsilon___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltEpsilon(lean_object*);
lean_object* l_Nat_cast___at_____private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
static lean_object* l_HC4_Newton_finiteTiltEpsilon___closed__1;
static lean_object* _init_l_HC4_Newton_finiteTiltEpsilon___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_cast___at_____private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Newton_finiteTiltEpsilon___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Nat_cast___at_____private_Std_Time_Format_Basic_0__Std_Time_toIsoString_spec__0(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltEpsilon(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_HC4_Newton_finiteTiltEpsilon___closed__0;
x_3 = l_HC4_Newton_finiteTiltEpsilon___closed__1;
x_4 = l_Rat_add(x_1, x_2);
x_5 = l_Rat_mul(x_3, x_4);
x_6 = l_Rat_div(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltedValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Rat_mul(x_1, x_3);
x_5 = l_Rat_add(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltedValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_finiteTiltedValue(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_SmithExtremeBalance(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_FiniteValuationTilt(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_SmithExtremeBalance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_finiteTiltEpsilon___closed__0 = _init_l_HC4_Newton_finiteTiltEpsilon___closed__0();
lean_mark_persistent(l_HC4_Newton_finiteTiltEpsilon___closed__0);
l_HC4_Newton_finiteTiltEpsilon___closed__1 = _init_l_HC4_Newton_finiteTiltEpsilon___closed__1();
lean_mark_persistent(l_HC4_Newton_finiteTiltEpsilon___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
