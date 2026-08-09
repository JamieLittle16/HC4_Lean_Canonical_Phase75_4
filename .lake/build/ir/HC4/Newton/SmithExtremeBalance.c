// Lean compiler output
// Module: HC4.Newton.SmithExtremeBalance
// Imports: Init HC4.Newton.SmithGradeArithmetic Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparator___boxed(lean_object*, lean_object*);
static lean_object* l_HC4_Newton_smithNegativeFirstExtreme___closed__1;
static lean_object* l_HC4_Newton_smithExtremeSeparator___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeDot(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithNegativeSecondExtreme(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithNegativeFirstExtreme(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* l_HC4_Newton_smithNegativeFirstExtreme___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeDot___boxed(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* _init_l_HC4_Newton_smithNegativeFirstExtreme___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Newton_smithNegativeFirstExtreme___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Newton_smithNegativeFirstExtreme___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithNegativeFirstExtreme(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_HC4_Newton_smithNegativeFirstExtreme___closed__1;
x_3 = lean_nat_to_int(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithNegativeSecondExtreme(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_HC4_Newton_smithNegativeFirstExtreme___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeDot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_int_mul(x_3, x_5);
x_8 = lean_int_mul(x_4, x_6);
x_9 = lean_int_add(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeDot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_smithGradeDot(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Newton_smithExtremeSeparator___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparator(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_HC4_Newton_smithExtremeSeparator___closed__0;
lean_inc(x_1);
x_4 = lean_nat_to_int(x_1);
x_5 = lean_int_mul(x_3, x_4);
lean_dec(x_4);
x_6 = lean_nat_mul(x_1, x_2);
lean_dec(x_1);
x_7 = lean_nat_to_int(x_6);
x_8 = l_HC4_Newton_smithNegativeFirstExtreme___closed__0;
x_9 = lean_int_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithExtremeSeparator___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_smithExtremeSeparator(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_SmithGradeArithmetic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_SmithExtremeBalance(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_SmithGradeArithmetic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_smithNegativeFirstExtreme___closed__0 = _init_l_HC4_Newton_smithNegativeFirstExtreme___closed__0();
lean_mark_persistent(l_HC4_Newton_smithNegativeFirstExtreme___closed__0);
l_HC4_Newton_smithNegativeFirstExtreme___closed__1 = _init_l_HC4_Newton_smithNegativeFirstExtreme___closed__1();
lean_mark_persistent(l_HC4_Newton_smithNegativeFirstExtreme___closed__1);
l_HC4_Newton_smithExtremeSeparator___closed__0 = _init_l_HC4_Newton_smithExtremeSeparator___closed__0();
lean_mark_persistent(l_HC4_Newton_smithExtremeSeparator___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
