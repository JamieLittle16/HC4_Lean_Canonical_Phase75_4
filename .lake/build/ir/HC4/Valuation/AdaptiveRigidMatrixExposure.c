// Lean compiler output
// Module: HC4.Valuation.AdaptiveRigidMatrixExposure
// Imports: Init HC4.Valuation.AdaptiveDiagonalExposure HC4.Valuation.RigidPacketZeroSchurBridge HC4.Valuation.CommonParameterFactorRestart Mathlib.Tactic
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
static lean_object* l_HC4_Valuation_rigidMatrixNormalizationExponent___closed__0;
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalDerivativeWeight___boxed(lean_object*);
lean_object* l_Field_toDivisionRing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidMatrixNormalizationExponent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidMatrixNormalizationExponent(lean_object*, lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalUnitPoint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalDerivativeWeight(lean_object*);
static lean_object* l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg___closed__0;
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = l_Field_toDivisionRing___redArg(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = l_Ring_toAddGroupWithOne___redArg(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalUnitPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalDerivativeWeight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg___closed__0;
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(1u);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidLongitudinalDerivativeWeight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_rigidLongitudinalDerivativeWeight(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Valuation_rigidMatrixNormalizationExponent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidMatrixNormalizationExponent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_HC4_Valuation_rigidMatrixNormalizationExponent___closed__0;
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_rigidMatrixNormalizationExponent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_rigidMatrixNormalizationExponent(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveDiagonalExposure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_RigidPacketZeroSchurBridge(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_CommonParameterFactorRestart(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveRigidMatrixExposure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveDiagonalExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_RigidPacketZeroSchurBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_CommonParameterFactorRestart(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg___closed__0 = _init_l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg___closed__0();
lean_mark_persistent(l_HC4_Valuation_rigidLongitudinalUnitPoint___redArg___closed__0);
l_HC4_Valuation_rigidMatrixNormalizationExponent___closed__0 = _init_l_HC4_Valuation_rigidMatrixNormalizationExponent___closed__0();
lean_mark_persistent(l_HC4_Valuation_rigidMatrixNormalizationExponent___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
