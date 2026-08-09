// Lean compiler output
// Module: HC4.Newton.TerminalTwoZeroPlanarisation
// Imports: Init HC4.Newton.TerminalTwoZeroEndpointInterface HC4.PlanarJC2Interface Mathlib.Algebra.MvPolynomial.Rename Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_standardJoinPoint___redArg___closed__1;
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardZeroPairEmbedding___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardZeroPairEmbedding;
static lean_object* l_HC4_Newton_standardJoinPoint___redArg___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardZeroPairEmbedding___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardZeroPairEmbedding___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_HC4_Newton_standardZeroPairEmbedding() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_HC4_Newton_standardZeroPairEmbedding___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardZeroPairEmbedding___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_standardZeroPairEmbedding___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_inc_ref(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Newton_standardPlanarPairMap___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_standardPlanarPairMap___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardPlanarPairMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Newton_standardPlanarPairMap(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l_HC4_Newton_standardJoinPoint___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Newton_standardJoinPoint___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_HC4_Newton_standardJoinPoint___redArg___closed__0;
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_nat_dec_eq(x_9, x_3);
if (x_10 == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = l_HC4_Newton_standardJoinPoint___redArg___closed__1;
x_13 = lean_apply_1(x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_15 = lean_nat_dec_eq(x_14, x_3);
lean_dec(x_14);
if (x_15 == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = l_HC4_Newton_standardJoinPoint___redArg___closed__0;
x_18 = lean_apply_1(x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec_ref(x_1);
x_20 = l_HC4_Newton_standardJoinPoint___redArg___closed__1;
x_21 = lean_apply_1(x_19, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_standardJoinPoint___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_standardJoinPoint___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardJoinPoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_standardJoinPoint(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalTwoZeroEndpointInterface(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_PlanarJC2Interface(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_MvPolynomial_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_TerminalTwoZeroPlanarisation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalTwoZeroEndpointInterface(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_PlanarJC2Interface(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_MvPolynomial_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_standardZeroPairEmbedding = _init_l_HC4_Newton_standardZeroPairEmbedding();
lean_mark_persistent(l_HC4_Newton_standardZeroPairEmbedding);
l_HC4_Newton_standardJoinPoint___redArg___closed__0 = _init_l_HC4_Newton_standardJoinPoint___redArg___closed__0();
lean_mark_persistent(l_HC4_Newton_standardJoinPoint___redArg___closed__0);
l_HC4_Newton_standardJoinPoint___redArg___closed__1 = _init_l_HC4_Newton_standardJoinPoint___redArg___closed__1();
lean_mark_persistent(l_HC4_Newton_standardJoinPoint___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
