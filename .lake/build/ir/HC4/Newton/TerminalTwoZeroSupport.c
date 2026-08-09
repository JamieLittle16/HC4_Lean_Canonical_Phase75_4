// Lean compiler output
// Module: HC4.Newton.TerminalTwoZeroSupport
// Imports: Init HC4.Newton.TerminalTwoZeroPattern HC4.Newton.CharZeroHessianKernelRigidity Mathlib.RingTheory.MvPolynomial.EulerIdentity Mathlib.Tactic
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
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairWeight___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairWeight(lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairWeight(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_dec_eq(x_5, x_2);
if (x_6 == 1)
{
lean_dec(x_5);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_8 = lean_nat_dec_eq(x_7, x_2);
lean_dec(x_7);
if (x_8 == 1)
{
return x_4;
}
else
{
return x_4;
}
}
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairWeight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_standardPositivePairWeight(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
if (x_10 == 1)
{
lean_dec(x_9);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_11, x_6);
lean_dec(x_11);
if (x_12 == 1)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardTwoZeroTerminalWeight_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 1)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
if (x_10 == 1)
{
lean_dec(x_9);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_11, x_6);
lean_dec(x_11);
if (x_12 == 1)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_HC4_Newton_TerminalTwoZeroSupport_0__HC4_Newton_standardPositivePairWeight_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalTwoZeroPattern(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_CharZeroHessianKernelRigidity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_RingTheory_MvPolynomial_EulerIdentity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_TerminalTwoZeroSupport(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalTwoZeroPattern(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_CharZeroHessianKernelRigidity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_RingTheory_MvPolynomial_EulerIdentity(builtin, lean_io_mk_world());
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
