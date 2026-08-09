// Lean compiler output
// Module: HC4.Newton.FirstSchurEntry
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
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_coefficient(lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_scale(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_scale___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_coefficient___redArg(lean_object*, lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_scale___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Field_toEuclideanDomain___redArg(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_CommRing_toNonUnitalCommRing___redArg(x_5);
x_7 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_6);
x_8 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_inc(x_2);
x_14 = lean_apply_2(x_9, x_2, x_11);
lean_inc(x_9);
lean_inc(x_2);
x_15 = lean_apply_2(x_9, x_2, x_12);
x_16 = lean_apply_2(x_9, x_2, x_13);
lean_ctor_set(x_3, 2, x_16);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_2);
x_20 = lean_apply_2(x_9, x_2, x_17);
lean_inc(x_9);
lean_inc(x_2);
x_21 = lean_apply_2(x_9, x_2, x_18);
x_22 = lean_apply_2(x_9, x_2, x_19);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurBlock_scale(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_BinarySchurBlock_scale___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_FirstBinarySchurEntry_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_coefficient___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_HC4_Newton_BinarySchurBlock_scale___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurEntry_coefficient(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_FirstBinarySchurEntry_coefficient___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_BinarySchurPivot(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_FirstSchurEntry(uint8_t builtin, lean_object* w) {
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
