// Lean compiler output
// Module: HC4.RationalRigidity.FinitePreimage
// Imports: Init HC4.RationalRigidity.ChartCertificates Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_rationalInfinityValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_rationalInfinityValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_infinityTargetValue___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_DivisionRing_toDivInvMonoid___redArg(lean_object*);
lean_object* l_Field_toDivisionRing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_infinityTargetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Polynomial_leadingCoeff___redArg(lean_object*);
lean_object* l_Polynomial_natDegree___redArg(lean_object*);
lean_object* l_Polynomial_coeff___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_rationalInfinityValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Field_toDivisionRing___redArg(x_1);
x_5 = l_DivisionRing_toDivInvMonoid___redArg(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
lean_inc_ref(x_3);
x_7 = l_Polynomial_natDegree___redArg(x_3);
x_8 = l_Polynomial_coeff___redArg(x_2, x_7);
x_9 = l_Polynomial_leadingCoeff___redArg(x_3);
x_10 = lean_apply_2(x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_rationalInfinityValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_RationalRigidity_rationalInfinityValue___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_RationalRigidity_finiteTargetValue___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_finiteTargetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_RationalRigidity_finiteTargetValue(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_infinityTargetValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_RationalRigidity_rationalInfinityValue___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_RationalRigidity_infinityTargetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_RationalRigidity_rationalInfinityValue___redArg(x_2, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_ChartCertificates(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_RationalRigidity_FinitePreimage(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_ChartCertificates(builtin, lean_io_mk_world());
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
