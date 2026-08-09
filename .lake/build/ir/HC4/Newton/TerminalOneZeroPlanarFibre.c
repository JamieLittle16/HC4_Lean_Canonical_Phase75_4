// Lean compiler output
// Module: HC4.Newton.TerminalOneZeroPlanarFibre
// Imports: Init HC4.Newton.TerminalOneZeroTransverseConstant HC4.PlanarJC2Interface Mathlib.Algebra.MvPolynomial.PDeriv Mathlib.Algebra.MvPolynomial.Rename Mathlib.Tactic
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
static lean_object* l_HC4_Newton_oneZeroSplitIndex___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
static lean_object* l_HC4_Newton_oneZeroSplitIndex___closed__5;
static lean_object* l_HC4_Newton_oneZeroSplitIndex___closed__4;
static lean_object* l_HC4_Newton_oneZeroSplitIndex___closed__1;
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
static lean_object* l_HC4_Newton_oneZeroSplitIndex___closed__2;
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_oneZeroSplitIndex___closed__3;
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroSplitIndex___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroSplitIndex(lean_object*);
static lean_object* _init_l_HC4_Newton_oneZeroSplitIndex___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Newton_oneZeroSplitIndex___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Newton_oneZeroSplitIndex___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Newton_oneZeroSplitIndex___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Newton_oneZeroSplitIndex___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Newton_oneZeroSplitIndex___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Newton_oneZeroSplitIndex___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Newton_oneZeroSplitIndex___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Newton_oneZeroSplitIndex___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Newton_oneZeroSplitIndex___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroSplitIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = l_HC4_Newton_oneZeroSplitIndex___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_nat_dec_eq(x_6, x_2);
if (x_7 == 1)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = l_HC4_Newton_oneZeroSplitIndex___closed__3;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_nat_sub(x_6, x_5);
lean_dec(x_6);
x_10 = lean_nat_dec_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 1)
{
lean_object* x_11; 
x_11 = l_HC4_Newton_oneZeroSplitIndex___closed__4;
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_HC4_Newton_oneZeroSplitIndex___closed__5;
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroSplitIndex___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_oneZeroSplitIndex(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_HC4_Newton_TerminalOneZeroPlanarFibre_0__HC4_Newton_oneZeroSplitIndex_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Field_toEuclideanDomain___redArg(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_CommRing_toNonUnitalCommRing___redArg(x_5);
x_7 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_6);
x_8 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 1)
{
lean_dec(x_9);
lean_inc(x_2);
return x_2;
}
else
{
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_oneZeroFrozenParameter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_oneZeroFrozenParameter___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroFrozenParameter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_oneZeroFrozenParameter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalOneZeroTransverseConstant(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_PlanarJC2Interface(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_MvPolynomial_PDeriv(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_MvPolynomial_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_TerminalOneZeroPlanarFibre(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalOneZeroTransverseConstant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_PlanarJC2Interface(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_MvPolynomial_PDeriv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_MvPolynomial_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_oneZeroSplitIndex___closed__0 = _init_l_HC4_Newton_oneZeroSplitIndex___closed__0();
lean_mark_persistent(l_HC4_Newton_oneZeroSplitIndex___closed__0);
l_HC4_Newton_oneZeroSplitIndex___closed__1 = _init_l_HC4_Newton_oneZeroSplitIndex___closed__1();
lean_mark_persistent(l_HC4_Newton_oneZeroSplitIndex___closed__1);
l_HC4_Newton_oneZeroSplitIndex___closed__2 = _init_l_HC4_Newton_oneZeroSplitIndex___closed__2();
lean_mark_persistent(l_HC4_Newton_oneZeroSplitIndex___closed__2);
l_HC4_Newton_oneZeroSplitIndex___closed__3 = _init_l_HC4_Newton_oneZeroSplitIndex___closed__3();
lean_mark_persistent(l_HC4_Newton_oneZeroSplitIndex___closed__3);
l_HC4_Newton_oneZeroSplitIndex___closed__4 = _init_l_HC4_Newton_oneZeroSplitIndex___closed__4();
lean_mark_persistent(l_HC4_Newton_oneZeroSplitIndex___closed__4);
l_HC4_Newton_oneZeroSplitIndex___closed__5 = _init_l_HC4_Newton_oneZeroSplitIndex___closed__5();
lean_mark_persistent(l_HC4_Newton_oneZeroSplitIndex___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
