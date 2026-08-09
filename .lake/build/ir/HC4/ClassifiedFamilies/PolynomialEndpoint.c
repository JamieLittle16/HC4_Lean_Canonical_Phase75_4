// Lean compiler output
// Module: HC4.ClassifiedFamilies.PolynomialEndpoint
// Imports: Init HC4.ClassifiedFamilies.ClassifiedEquiv Mathlib
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
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rPolynomialPotentialValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_s_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_s_elim___redArg(lean_object*, lean_object*);
lean_object* l_HC4_ClassifiedFamilies_sValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_Polynomial_eval___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_r_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rPolynomialPotentialValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_s_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sPolynomialPotentialValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_r_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sPolynomialPotentialValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___redArg___boxed(lean_object*);
lean_object* l_HC4_ClassifiedFamilies_rValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_r_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rPolynomialPotentialValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_1);
x_6 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_7 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_6);
x_8 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
lean_inc(x_9);
lean_inc(x_14);
lean_inc(x_11);
x_16 = lean_apply_2(x_9, x_11, x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_apply_2(x_9, x_12, x_13);
lean_inc(x_10);
x_18 = lean_apply_2(x_10, x_16, x_17);
x_19 = l_HC4_ClassifiedFamilies_rValue___redArg(x_1, x_2, x_3, x_5);
x_20 = l_Polynomial_eval___redArg(x_15, x_19, x_4);
x_21 = lean_apply_2(x_10, x_18, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rPolynomialPotentialValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_rPolynomialPotentialValue___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sPolynomialPotentialValue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_1);
x_6 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_7 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_6);
x_8 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
lean_inc(x_9);
lean_inc(x_14);
lean_inc(x_11);
x_16 = lean_apply_2(x_9, x_11, x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_apply_2(x_9, x_12, x_13);
lean_inc(x_10);
x_18 = lean_apply_2(x_10, x_16, x_17);
x_19 = l_HC4_ClassifiedFamilies_sValue___redArg(x_1, x_2, x_3, x_5);
x_20 = l_Polynomial_eval___redArg(x_15, x_19, x_4);
x_21 = lean_apply_2(x_10, x_18, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sPolynomialPotentialValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_sPolynomialPotentialValue___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_r_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_r_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_r_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_PolynomialBranch_r_elim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_s_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_s_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_PolynomialBranch_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_PolynomialBranch_s_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_PolynomialBranch_s_elim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_ClassifiedFamilies_ClassifiedEquiv(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_ClassifiedFamilies_PolynomialEndpoint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_ClassifiedFamilies_ClassifiedEquiv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
