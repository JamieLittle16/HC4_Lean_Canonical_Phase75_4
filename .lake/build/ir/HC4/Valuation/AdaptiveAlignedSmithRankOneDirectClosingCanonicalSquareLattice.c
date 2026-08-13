// Lean compiler output
// Module: HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingCanonicalSquareLattice
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingSquareContactSource Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareCommonLevel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareRamification;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareCommonLevel(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___closed__0;
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_mul(x_9, x_1);
return x_10;
}
else
{
return x_4;
}
}
else
{
return x_4;
}
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_3, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mul(x_12, x_1);
return x_13;
}
else
{
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareRamification() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareCommonLevel(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareCommonLevel___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareCommonLevel(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithRankOneDirectClosingSquareContactSource(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithRankOneDirectClosingCanonicalSquareLattice(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithRankOneDirectClosingSquareContactSource(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___closed__0 = _init_l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___closed__0();
lean_mark_persistent(l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareWeight___closed__0);
l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareRamification = _init_l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareRamification();
lean_mark_persistent(l_HC4_Valuation_AdaptiveAlignedSmithRankOneClosingSourceCarrier_directClosingCanonicalSquareRamification);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
