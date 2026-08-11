// Lean compiler output
// Module: HC4.Valuation.AdaptiveDiagonalExposure
// Imports: Init HC4.Newton.AdaptivePacketExposure HC4.Valuation.PrimitiveSmithEndpoint Mathlib.Tactic
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
static lean_object* l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__0;
lean_object* l_HC4_Polynomial_ordinaryDegree4(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_adaptiveDiagonalRawExponent___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_adaptiveDiagonalRawExponent(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__2;
static lean_object* l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_adaptiveDiagonalRawExponent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_HC4_Polynomial_ordinaryDegree4(x_2);
x_5 = l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__0;
lean_inc(x_3);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__1;
lean_inc(x_3);
x_9 = lean_apply_1(x_3, x_8);
x_10 = lean_nat_add(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__2;
x_12 = lean_apply_1(x_3, x_11);
x_13 = lean_nat_mul(x_7, x_12);
lean_dec(x_12);
x_14 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = lean_nat_mul(x_1, x_14);
lean_dec(x_14);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_15);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_adaptiveDiagonalRawExponent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_adaptiveDiagonalRawExponent(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_AdaptivePacketExposure(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_PrimitiveSmithEndpoint(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveDiagonalExposure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_AdaptivePacketExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_PrimitiveSmithEndpoint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__0 = _init_l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__0();
lean_mark_persistent(l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__0);
l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__1 = _init_l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__1();
lean_mark_persistent(l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__1);
l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__2 = _init_l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__2();
lean_mark_persistent(l_HC4_Valuation_adaptiveDiagonalRawExponent___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
