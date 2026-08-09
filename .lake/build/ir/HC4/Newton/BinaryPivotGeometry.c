// Lean compiler output
// Module: HC4.Newton.BinaryPivotGeometry
// Imports: Init HC4.Newton.BinarySchurPivot Mathlib.Tactic
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
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* l_Field_toDivisionRing___redArg(lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_quadratic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_quadratic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_quadratic___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_1);
x_5 = l_Field_toEuclideanDomain___redArg(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_CommRing_toNonUnitalCommRing___redArg(x_6);
x_8 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_7);
x_9 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = l_Field_toDivisionRing___redArg(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_15);
x_17 = l_Ring_toAddGroupWithOne___redArg(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_10);
lean_inc(x_3);
x_20 = lean_apply_2(x_10, x_12, x_3);
lean_inc(x_10);
lean_inc(x_3);
x_21 = lean_apply_2(x_10, x_20, x_3);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_apply_1(x_19, x_22);
lean_inc(x_10);
x_24 = lean_apply_2(x_10, x_23, x_13);
lean_inc(x_10);
x_25 = lean_apply_2(x_10, x_24, x_3);
lean_inc(x_10);
lean_inc(x_4);
x_26 = lean_apply_2(x_10, x_25, x_4);
lean_inc(x_11);
x_27 = lean_apply_2(x_11, x_21, x_26);
lean_inc(x_10);
lean_inc(x_4);
x_28 = lean_apply_2(x_10, x_14, x_4);
x_29 = lean_apply_2(x_10, x_28, x_4);
x_30 = lean_apply_2(x_11, x_27, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_quadratic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Newton_BinarySchurBlock_quadratic___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_BinarySchurPivot(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_BinaryPivotGeometry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_BinarySchurPivot(builtin, lean_io_mk_world());
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
