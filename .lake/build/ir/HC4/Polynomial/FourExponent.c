// Lean compiler output
// Module: HC4.Polynomial.FourExponent
// Imports: Init HC4.Polynomial.WeightedInitial HC4.Toric.Facets
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
LEAN_EXPORT lean_object* l_HC4_Polynomial_facetOmittedCoordinate(uint8_t);
static lean_object* l_HC4_Polynomial_toToricExponent___closed__0;
LEAN_EXPORT lean_object* l_HC4_Polynomial_facetOmittedCoordinate___boxed(lean_object*);
static lean_object* l_HC4_Polynomial_toToricExponent___closed__3;
static lean_object* l_HC4_Polynomial_toToricExponent___closed__2;
static lean_object* l_HC4_Polynomial_toToricExponent___closed__1;
LEAN_EXPORT lean_object* l_HC4_Polynomial_toToricExponent(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Polynomial_ordinaryDegree4(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Polynomial_toToricExponent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Polynomial_toToricExponent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Polynomial_toToricExponent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Polynomial_toToricExponent___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_toToricExponent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_HC4_Polynomial_toToricExponent___closed__0;
lean_inc(x_2);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_HC4_Polynomial_toToricExponent___closed__1;
lean_inc(x_2);
x_6 = lean_apply_1(x_2, x_5);
x_7 = l_HC4_Polynomial_toToricExponent___closed__2;
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
x_9 = l_HC4_Polynomial_toToricExponent___closed__3;
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_ordinaryDegree4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_HC4_Polynomial_toToricExponent___closed__0;
lean_inc(x_2);
x_4 = lean_apply_1(x_2, x_3);
x_5 = l_HC4_Polynomial_toToricExponent___closed__1;
lean_inc(x_2);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_8 = l_HC4_Polynomial_toToricExponent___closed__2;
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_nat_add(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
x_11 = l_HC4_Polynomial_toToricExponent___closed__3;
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_nat_add(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_facetOmittedCoordinate(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_HC4_Polynomial_toToricExponent___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_HC4_Polynomial_toToricExponent___closed__3;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_HC4_Polynomial_toToricExponent___closed__0;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_HC4_Polynomial_toToricExponent___closed__2;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_HC4_Polynomial_facetOmittedCoordinate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_HC4_Polynomial_facetOmittedCoordinate(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_WeightedInitial(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_Facets(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial_FourExponent(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_WeightedInitial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_Facets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Polynomial_toToricExponent___closed__0 = _init_l_HC4_Polynomial_toToricExponent___closed__0();
lean_mark_persistent(l_HC4_Polynomial_toToricExponent___closed__0);
l_HC4_Polynomial_toToricExponent___closed__1 = _init_l_HC4_Polynomial_toToricExponent___closed__1();
lean_mark_persistent(l_HC4_Polynomial_toToricExponent___closed__1);
l_HC4_Polynomial_toToricExponent___closed__2 = _init_l_HC4_Polynomial_toToricExponent___closed__2();
lean_mark_persistent(l_HC4_Polynomial_toToricExponent___closed__2);
l_HC4_Polynomial_toToricExponent___closed__3 = _init_l_HC4_Polynomial_toToricExponent___closed__3();
lean_mark_persistent(l_HC4_Polynomial_toToricExponent___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
