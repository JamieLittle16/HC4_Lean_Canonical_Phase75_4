// Lean compiler output
// Module: HC4.Newton.PositiveWeightTriangularEvaluation
// Imports: Init HC4.Newton.TerminalPositiveWeightLinearBlocks Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AddGroupWithOne_toAddGroup___redArg(lean_object*);
lean_object* l_Field_toDivisionRing___redArg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPointDifference(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPointDifference___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPointDifference___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Field_toDivisionRing___redArg(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Ring_toAddGroupWithOne___redArg(x_6);
x_8 = l_AddGroupWithOne_toAddGroup___redArg(x_7);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_4);
x_10 = lean_apply_1(x_2, x_4);
x_11 = lean_apply_1(x_3, x_4);
x_12 = lean_apply_2(x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPointDifference(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Newton_terminalPointDifference___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_6);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_int_dec_eq(x_7, x_3);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = l_Field_toEuclideanDomain___redArg(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = l_CommRing_toNonUnitalCommRing___redArg(x_10);
x_12 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_11);
x_13 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l_Field_toDivisionRing___redArg(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_17 = l_Ring_toAddGroupWithOne___redArg(x_16);
x_18 = l_AddGroupWithOne_toAddGroup___redArg(x_17);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_6);
x_20 = lean_apply_1(x_4, x_6);
x_21 = lean_apply_1(x_5, x_6);
x_22 = lean_apply_2(x_19, x_20, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_Newton_terminalWeightSliceDifference___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_Newton_terminalWeightSliceDifference___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_terminalWeightSliceDifference___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_Newton_terminalWeightSliceDifference(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalPositiveWeightLinearBlocks(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_PositiveWeightTriangularEvaluation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalPositiveWeightLinearBlocks(builtin, lean_io_mk_world());
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
