// Lean compiler output
// Module: HC4.Newton.SmithValuationTiltAdapter
// Imports: Init HC4.Newton.FiniteValuationTilt Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_grade___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithNormalisedConformalTiltChange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithNormalisedConformalTiltChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_Newton_smithExtremeSeparator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparatorBound(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_HC4_Newton_instDecidableEqSmithSupportExponent(lean_object*, lean_object*);
lean_object* l_HC4_Newton_smithGradeDot(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithRawConformalTiltChange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_instDecidableEqSmithSupportExponent_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_grade(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithSeparatorDelta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithSeparatorDelta___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_ctorIdx___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithLeviNormalisationTiltChange___boxed(lean_object*);
lean_object* l_HC4_Newton_smithGrade(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithRawConformalTiltChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_instDecidableEqSmithSupportExponent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithLeviNormalisationTiltChange(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparatorBound___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_HC4_Newton_instDecidableEqSmithSupportExponent_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithRawConformalTiltChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_to_int(x_2);
x_8 = lean_int_mul(x_5, x_7);
lean_dec(x_7);
x_9 = lean_nat_to_int(x_3);
x_10 = lean_int_mul(x_6, x_9);
lean_dec(x_9);
x_11 = lean_int_add(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
x_12 = lean_int_add(x_5, x_6);
x_13 = lean_nat_to_int(x_4);
x_14 = lean_int_mul(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_int_add(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithRawConformalTiltChange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_smithRawConformalTiltChange(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithLeviNormalisationTiltChange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_int_add(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithLeviNormalisationTiltChange___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_smithLeviNormalisationTiltChange(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithNormalisedConformalTiltChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_HC4_Newton_smithRawConformalTiltChange(x_1, x_2, x_3, x_4);
x_6 = l_HC4_Newton_smithLeviNormalisationTiltChange(x_1);
x_7 = lean_int_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithNormalisedConformalTiltChange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_smithNormalisedConformalTiltChange(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparatorBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_3, x_1);
x_5 = lean_nat_mul(x_1, x_2);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparatorBound___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_smithExtremeSeparatorBound(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_SmithSupportExponent_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_HC4_Newton_instDecidableEqSmithSupportExponent_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_eq(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_5, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_instDecidableEqSmithSupportExponent_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HC4_Newton_instDecidableEqSmithSupportExponent_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_HC4_Newton_instDecidableEqSmithSupportExponent(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_HC4_Newton_instDecidableEqSmithSupportExponent_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_instDecidableEqSmithSupportExponent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HC4_Newton_instDecidableEqSmithSupportExponent(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_grade(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_HC4_Newton_smithGrade(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_SmithSupportExponent_grade___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_SmithSupportExponent_grade(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithSeparatorDelta(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_HC4_Newton_smithExtremeSeparator(x_1, x_2);
x_5 = l_HC4_Newton_SmithSupportExponent_grade(x_3);
x_6 = l_HC4_Newton_smithGradeDot(x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithSeparatorDelta___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_smithSeparatorDelta(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FiniteValuationTilt(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_SmithValuationTiltAdapter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FiniteValuationTilt(builtin, lean_io_mk_world());
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
