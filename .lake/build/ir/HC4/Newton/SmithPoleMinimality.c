// Lean compiler output
// Module: HC4.Newton.SmithPoleMinimality
// Imports: Init HC4.Newton.SmithValuationTiltAdapter Mathlib.Tactic
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
lean_object* l_HC4_Newton_smithExtremeSeparatorBound(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithIntegralSeparatorTilt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltDenominator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithRescaledOldMinimum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltDenominator(lean_object*);
lean_object* l_HC4_Newton_smithSeparatorDelta(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithRescaledOldMinimum___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_finiteIntegralRescaledTilt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_finiteIntegralRescaledTilt(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithIntegralSeparatorTilt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltDenominator(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_nat_mul(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_finiteTiltDenominator___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_finiteTiltDenominator(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_finiteIntegralRescaledTilt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_HC4_Newton_finiteTiltDenominator(x_1);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_mul(x_5, x_2);
lean_dec(x_5);
x_7 = lean_int_add(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_finiteIntegralRescaledTilt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_finiteIntegralRescaledTilt(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithIntegralSeparatorTilt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_HC4_Newton_smithExtremeSeparatorBound(x_1, x_2);
lean_inc_ref(x_4);
x_6 = lean_apply_1(x_3, x_4);
x_7 = l_HC4_Newton_smithSeparatorDelta(x_1, x_2, x_4);
lean_dec_ref(x_4);
x_8 = l_HC4_Newton_finiteIntegralRescaledTilt(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithIntegralSeparatorTilt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_smithIntegralSeparatorTilt(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithRescaledOldMinimum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_HC4_Newton_smithExtremeSeparatorBound(x_1, x_2);
x_5 = l_HC4_Newton_finiteTiltDenominator(x_4);
lean_dec(x_4);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_mul(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithRescaledOldMinimum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_smithRescaledOldMinimum(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_SmithValuationTiltAdapter(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_SmithPoleMinimality(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_SmithValuationTiltAdapter(builtin, lean_io_mk_world());
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
