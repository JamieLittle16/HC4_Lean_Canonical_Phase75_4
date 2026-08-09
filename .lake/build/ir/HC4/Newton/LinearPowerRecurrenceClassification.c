// Lean compiler output
// Module: HC4.Newton.LinearPowerRecurrenceClassification
// Imports: Init HC4.Newton.LinearPowerRecurrence Mathlib.Tactic
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
lean_object* l_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* l_SubNegZeroMonoid_toNegZeroClass___redArg(lean_object*);
lean_object* l_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* l_Field_toDivisionRing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_linearPowerScalar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toSemifield___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_linearPowerScalar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Ring_toAddCommGroup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_linearPowerScalar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc_ref(x_1);
x_5 = l_Field_toDivisionRing___redArg(x_1);
lean_inc_ref(x_5);
x_6 = l_DivisionRing_toDivInvMonoid___redArg(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Field_toSemifield___redArg(x_1);
lean_dec_ref(x_1);
x_9 = l_Semifield_toDivisionSemiring___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_5);
x_12 = l_Ring_toAddCommGroup___redArg(x_11);
x_13 = l_SubNegZeroMonoid_toNegZeroClass___redArg(x_12);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_10, 3);
lean_inc(x_15);
lean_dec_ref(x_10);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_apply_1(x_4, x_16);
x_18 = lean_apply_1(x_14, x_2);
x_19 = lean_apply_2(x_15, x_3, x_18);
x_20 = lean_apply_2(x_7, x_17, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_linearPowerScalar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Newton_linearPowerScalar___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_LinearPowerRecurrence(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_LinearPowerRecurrenceClassification(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_LinearPowerRecurrence(builtin, lean_io_mk_world());
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
