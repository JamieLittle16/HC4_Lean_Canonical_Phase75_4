// Lean compiler output
// Module: HC4.Newton.FirstSchurDeterminantOrder
// Imports: Init HC4.Newton.FirstSchurEntry Mathlib.Algebra.Polynomial.Basic Mathlib.Tactic
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
lean_object* l_Semifield_toDivisionSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_entryBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurFamilyEntry_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_entryBlock___redArg(lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_Polynomial_eval___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurFamilyEntry_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toSemifield___redArg(lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_BinarySchurTail_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_entryBlock___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_3 = l_Field_toSemifield___redArg(x_1);
x_4 = l_Semifield_toDivisionSemiring___redArg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Field_toEuclideanDomain___redArg(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_CommRing_toNonUnitalCommRing___redArg(x_7);
x_9 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_8);
x_10 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_inc_ref(x_5);
x_16 = l_Polynomial_eval___redArg(x_5, x_11, x_13);
lean_inc(x_11);
lean_inc_ref(x_5);
x_17 = l_Polynomial_eval___redArg(x_5, x_11, x_14);
x_18 = l_Polynomial_eval___redArg(x_5, x_11, x_15);
lean_ctor_set(x_2, 2, x_18);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_11);
lean_inc_ref(x_5);
x_22 = l_Polynomial_eval___redArg(x_5, x_11, x_19);
lean_inc(x_11);
lean_inc_ref(x_5);
x_23 = l_Polynomial_eval___redArg(x_5, x_11, x_20);
x_24 = l_Polynomial_eval___redArg(x_5, x_11, x_21);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_BinarySchurTail_entryBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_BinarySchurTail_entryBlock___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurFamilyEntry_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_FirstBinarySchurFamilyEntry_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_FirstBinarySchurFamilyEntry_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FirstSchurEntry(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_FirstSchurDeterminantOrder(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FirstSchurEntry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Basic(builtin, lean_io_mk_world());
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
