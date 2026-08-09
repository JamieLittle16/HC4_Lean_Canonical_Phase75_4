// Lean compiler output
// Module: HC4.QuasiTranslation.RankOneShear
// Imports: Init Mathlib
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
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearFlow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearInverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_displacement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearInverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_displacement___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearInverse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearFlow___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_displacement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearFlow___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_displacement___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_apply_2(x_1, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_displacement(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_QuasiTranslation_displacement___redArg(x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_displacement___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_QuasiTranslation_displacement(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_6);
x_9 = l_HC4_QuasiTranslation_displacement___redArg(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_apply_2(x_8, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_QuasiTranslation_shearMap___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_QuasiTranslation_shearMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearInverse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc(x_6);
x_8 = l_HC4_QuasiTranslation_displacement___redArg(x_2, x_3, x_4, x_5, x_6);
x_9 = lean_apply_2(x_7, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearInverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_QuasiTranslation_shearInverse___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearInverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_QuasiTranslation_shearInverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearFlow___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_2(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearFlow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_10 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_9);
x_11 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_alloc_closure((void*)(l_HC4_QuasiTranslation_shearFlow___redArg___lam__0), 4, 3);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_4);
x_14 = l_HC4_QuasiTranslation_shearMap___redArg(x_2, x_3, x_5, x_6, x_13, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_HC4_QuasiTranslation_shearFlow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_HC4_QuasiTranslation_shearFlow___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_QuasiTranslation_RankOneShear(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
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
