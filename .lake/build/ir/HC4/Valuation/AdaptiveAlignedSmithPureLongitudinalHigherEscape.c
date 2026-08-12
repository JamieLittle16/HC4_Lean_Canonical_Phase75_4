// Lean compiler output
// Module: HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalLinearEscape HC4.Polynomial.TopProduct HC4.Newton.CharZeroHessianKernelRigidity Mathlib.Tactic
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
static lean_object* l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__2;
static lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__2;
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport___redArg___lam__0___boxed(lean_object*);
static lean_object* l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__1;
lean_object* l_Multiset_filter___redArg(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__0;
LEAN_EXPORT lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight(lean_object*);
static lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__3;
static lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__1;
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_pureLongitudinalTransverseDegree(lean_object*);
LEAN_EXPORT uint8_t l_HC4_Valuation_positiveTransverseSourceSupport___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__0;
static lean_object* _init_l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_pureLongitudinalTransverseDegree(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__0;
lean_inc(x_2);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__1;
lean_inc(x_2);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_8 = l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__2;
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
return x_10;
}
}
static lean_object* _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__1;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__0;
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__3;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_pureLongitudinalTransverseWeight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_pureLongitudinalTransverseWeight(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_HC4_Valuation_positiveTransverseSourceSupport___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_HC4_Valuation_pureLongitudinalTransverseDegree(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_HC4_Valuation_positiveTransverseSourceSupport___redArg___lam__0___boxed), 1, 0);
x_4 = l_Multiset_filter___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_positiveTransverseSourceSupport___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_HC4_Valuation_positiveTransverseSourceSupport___redArg___lam__0(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_positiveTransverseSourceSupport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Valuation_positiveTransverseSourceSupport(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithPureLongitudinalLinearEscape(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_TopProduct(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_CharZeroHessianKernelRigidity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithPureLongitudinalHigherEscape(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithPureLongitudinalLinearEscape(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_TopProduct(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_CharZeroHessianKernelRigidity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__0 = _init_l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__0();
lean_mark_persistent(l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__0);
l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__1 = _init_l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__1();
lean_mark_persistent(l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__1);
l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__2 = _init_l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__2();
lean_mark_persistent(l_HC4_Valuation_pureLongitudinalTransverseDegree___closed__2);
l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__0 = _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__0();
lean_mark_persistent(l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__0);
l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__1 = _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__1();
lean_mark_persistent(l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__1);
l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__2 = _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__2();
lean_mark_persistent(l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__2);
l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__3 = _init_l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__3();
lean_mark_persistent(l_HC4_Valuation_pureLongitudinalTransverseWeight___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
