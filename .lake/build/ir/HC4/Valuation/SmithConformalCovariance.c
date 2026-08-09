// Lean compiler output
// Module: HC4.Valuation.SmithConformalCovariance
// Imports: Init HC4.Valuation.IntegralKernelSlopeExtraction HC4.Newton.SmithValuationTiltAdapter Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.MvPolynomial.Funext Mathlib.LinearAlgebra.Matrix.Determinant.Basic Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalSourceExponent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalMultiplierExponent(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_smithConformalSourceExponent___closed__0;
static lean_object* l_HC4_Valuation_smithConformalSourceExponent___closed__2;
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalRawExponent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalSourceExponent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalRawExponent___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_smithConformalSourceExponent___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalMultiplierExponent___boxed(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_smithConformalRawExponent___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_smithConformalSourceExponent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_smithConformalSourceExponent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_smithConformalSourceExponent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalSourceExponent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_HC4_Valuation_smithConformalSourceExponent___closed__0;
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_HC4_Valuation_smithConformalSourceExponent___closed__1;
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_HC4_Valuation_smithConformalSourceExponent___closed__2;
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_nat_add(x_1, x_2);
return x_11;
}
else
{
lean_inc(x_2);
return x_2;
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalSourceExponent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_smithConformalSourceExponent(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalMultiplierExponent(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalMultiplierExponent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_smithConformalMultiplierExponent(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_smithConformalRawExponent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalRawExponent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_HC4_Valuation_smithConformalSourceExponent___closed__1;
lean_inc(x_4);
x_6 = lean_apply_1(x_4, x_5);
x_7 = lean_nat_mul(x_1, x_6);
lean_dec(x_6);
x_8 = l_HC4_Valuation_smithConformalSourceExponent___closed__2;
lean_inc(x_4);
x_9 = lean_apply_1(x_4, x_8);
x_10 = lean_nat_mul(x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_add(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
x_12 = lean_nat_add(x_1, x_2);
x_13 = l_HC4_Valuation_smithConformalRawExponent___closed__0;
x_14 = lean_apply_1(x_4, x_13);
x_15 = lean_nat_mul(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = lean_nat_add(x_11, x_15);
lean_dec(x_15);
lean_dec(x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_smithConformalRawExponent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_smithConformalRawExponent(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_IntegralKernelSlopeExtraction(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_SmithValuationTiltAdapter(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Fin(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_MvPolynomial_Funext(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_SmithConformalCovariance(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_IntegralKernelSlopeExtraction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_SmithValuationTiltAdapter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Fin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_MvPolynomial_Funext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_smithConformalSourceExponent___closed__0 = _init_l_HC4_Valuation_smithConformalSourceExponent___closed__0();
lean_mark_persistent(l_HC4_Valuation_smithConformalSourceExponent___closed__0);
l_HC4_Valuation_smithConformalSourceExponent___closed__1 = _init_l_HC4_Valuation_smithConformalSourceExponent___closed__1();
lean_mark_persistent(l_HC4_Valuation_smithConformalSourceExponent___closed__1);
l_HC4_Valuation_smithConformalSourceExponent___closed__2 = _init_l_HC4_Valuation_smithConformalSourceExponent___closed__2();
lean_mark_persistent(l_HC4_Valuation_smithConformalSourceExponent___closed__2);
l_HC4_Valuation_smithConformalRawExponent___closed__0 = _init_l_HC4_Valuation_smithConformalRawExponent___closed__0();
lean_mark_persistent(l_HC4_Valuation_smithConformalRawExponent___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
