// Lean compiler output
// Module: HC4.Newton.SmithGradeArithmetic
// Imports: Init HC4.Newton.SmithCollisionQuadraticRankOne Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_smithGrade___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_smithGradeFirst___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeFirst(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeSecond___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithGrade(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeFirst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeSecond(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Newton_smithGradeFirst___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeFirst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_nat_to_int(x_3);
x_5 = l_HC4_Newton_smithGradeFirst___closed__0;
x_6 = lean_int_sub(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeFirst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_smithGradeFirst(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeSecond(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_nat_to_int(x_3);
x_5 = l_HC4_Newton_smithGradeFirst___closed__0;
x_6 = lean_int_sub(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGradeSecond___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_smithGradeSecond(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGrade(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_HC4_Newton_smithGradeFirst(x_1, x_3);
x_5 = l_HC4_Newton_smithGradeSecond(x_2, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_smithGrade___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_smithGrade(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_SmithCollisionQuadraticRankOne(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_SmithGradeArithmetic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_SmithCollisionQuadraticRankOne(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_smithGradeFirst___closed__0 = _init_l_HC4_Newton_smithGradeFirst___closed__0();
lean_mark_persistent(l_HC4_Newton_smithGradeFirst___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
