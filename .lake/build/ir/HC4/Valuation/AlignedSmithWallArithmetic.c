// Lean compiler output
// Module: HC4.Valuation.AlignedSmithWallArithmetic
// Imports: Init HC4.Valuation.ZeroSlopeSmithDispatcher Mathlib.Data.Finset.Max Mathlib.Algebra.Polynomial.Div Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithCoefficientValue___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_alignedSmithSectionValueTwo___closed__0;
static lean_object* l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__1;
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithSectionValueTwo(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__0;
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithNegativeCoefficientWall___boxed(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_alignedSmithSectionValueFour___closed__0;
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithNegativeCoefficientWall(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_HC4_Newton_smithSeparatorDelta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithRamificationIndex;
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithCoefficientValue(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_alignedSmithCoefficientValue___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithSectionValueFour(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_alignedSmithRamificationIndex() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(20u);
return x_1;
}
}
static lean_object* _init_l_HC4_Valuation_alignedSmithCoefficientValue___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(20u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithCoefficientValue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_HC4_Valuation_alignedSmithCoefficientValue___closed__0;
x_5 = lean_nat_to_int(x_1);
x_6 = lean_int_mul(x_4, x_5);
lean_dec(x_5);
x_7 = lean_nat_to_int(x_2);
x_8 = lean_int_mul(x_7, x_3);
lean_dec(x_7);
x_9 = lean_int_add(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithCoefficientValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_alignedSmithCoefficientValue(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_HC4_Valuation_alignedSmithSectionValueTwo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithSectionValueTwo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_HC4_Valuation_alignedSmithCoefficientValue___closed__0;
x_4 = lean_nat_to_int(x_1);
x_5 = lean_int_mul(x_3, x_4);
lean_dec(x_4);
x_6 = l_HC4_Valuation_alignedSmithSectionValueTwo___closed__0;
x_7 = lean_nat_to_int(x_2);
x_8 = lean_int_mul(x_6, x_7);
lean_dec(x_7);
x_9 = lean_int_sub(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
return x_9;
}
}
static lean_object* _init_l_HC4_Valuation_alignedSmithSectionValueFour___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithSectionValueFour(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_HC4_Valuation_alignedSmithCoefficientValue___closed__0;
x_4 = lean_nat_to_int(x_1);
x_5 = lean_int_mul(x_3, x_4);
lean_dec(x_4);
x_6 = l_HC4_Valuation_alignedSmithSectionValueFour___closed__0;
x_7 = lean_nat_to_int(x_2);
x_8 = lean_int_mul(x_6, x_7);
lean_dec(x_7);
x_9 = lean_int_sub(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
return x_9;
}
}
static lean_object* _init_l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Valuation_alignedSmithSectionValueFour___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Valuation_alignedSmithSectionValueTwo___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithNegativeCoefficientWall(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_HC4_Newton_smithSeparatorDelta(x_3, x_3, x_1);
x_5 = l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__0;
x_6 = lean_int_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__1;
x_8 = lean_int_dec_eq(x_4, x_7);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(10u);
x_11 = lean_nat_mul(x_10, x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_nat_mul(x_13, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_alignedSmithNegativeCoefficientWall___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_alignedSmithNegativeCoefficientWall(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_ZeroSlopeSmithDispatcher(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Finset_Max(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Div(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AlignedSmithWallArithmetic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_ZeroSlopeSmithDispatcher(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Max(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Div(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_alignedSmithRamificationIndex = _init_l_HC4_Valuation_alignedSmithRamificationIndex();
lean_mark_persistent(l_HC4_Valuation_alignedSmithRamificationIndex);
l_HC4_Valuation_alignedSmithCoefficientValue___closed__0 = _init_l_HC4_Valuation_alignedSmithCoefficientValue___closed__0();
lean_mark_persistent(l_HC4_Valuation_alignedSmithCoefficientValue___closed__0);
l_HC4_Valuation_alignedSmithSectionValueTwo___closed__0 = _init_l_HC4_Valuation_alignedSmithSectionValueTwo___closed__0();
lean_mark_persistent(l_HC4_Valuation_alignedSmithSectionValueTwo___closed__0);
l_HC4_Valuation_alignedSmithSectionValueFour___closed__0 = _init_l_HC4_Valuation_alignedSmithSectionValueFour___closed__0();
lean_mark_persistent(l_HC4_Valuation_alignedSmithSectionValueFour___closed__0);
l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__0 = _init_l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__0();
lean_mark_persistent(l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__0);
l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__1 = _init_l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__1();
lean_mark_persistent(l_HC4_Valuation_alignedSmithNegativeCoefficientWall___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
