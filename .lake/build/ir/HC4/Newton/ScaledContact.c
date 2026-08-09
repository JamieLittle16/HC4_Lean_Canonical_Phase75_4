// Lean compiler output
// Module: HC4.Newton.ScaledContact
// Imports: Init HC4.Polynomial.FourExponent HC4.MongeAmpere.FirstContactMaximal
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
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_HC4_Newton_scaledContactWeight___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_scaledContactWeight(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_scaledContactWeight___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_Polynomial_ordinaryDegree4(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_scaledContactExponentWeight(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Newton_scaledContactWeight___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_scaledContactWeight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_nat_to_int(x_2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = l_HC4_Newton_scaledContactWeight___closed__0;
x_8 = lean_int_add(x_5, x_7);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_nat_to_int(x_3);
x_10 = lean_int_add(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_scaledContactWeight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_scaledContactWeight(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_scaledContactExponentWeight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_nat_to_int(x_2);
x_7 = l_HC4_Polynomial_ordinaryDegree4(x_4);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_int_mul(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
x_10 = lean_nat_to_int(x_3);
x_11 = lean_apply_1(x_5, x_1);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_mul(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = lean_int_add(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
return x_14;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_FourExponent(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_MongeAmpere_FirstContactMaximal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_ScaledContact(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_FourExponent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_FirstContactMaximal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_scaledContactWeight___closed__0 = _init_l_HC4_Newton_scaledContactWeight___closed__0();
lean_mark_persistent(l_HC4_Newton_scaledContactWeight___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
