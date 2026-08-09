// Lean compiler output
// Module: HC4.PlanarDoublingInjectivity
// Imports: Init HC4.PlanarJC2Interface Mathlib.LinearAlgebra.Matrix.NonsingularInverse Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_doublingGradientMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
static lean_object* l_HC4_doublingGradientMap___redArg___lam__0___closed__0;
lean_object* l_Matrix_vecMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_doublingGradientMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* l_HC4_doublingGradientMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
static lean_object* _init_l_HC4_doublingGradientMap___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_List_finRange(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_doublingGradientMap___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_HC4_doublingGradientMap___redArg___lam__0___closed__0;
lean_inc(x_2);
x_9 = lean_apply_1(x_1, x_2);
lean_inc(x_7);
x_10 = l_Matrix_vecMul___redArg(x_3, x_8, x_4, x_9, x_7);
x_11 = lean_apply_2(x_5, x_2, x_7);
x_12 = lean_apply_2(x_6, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_HC4_doublingGradientMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = l_Field_toEuclideanDomain___redArg(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_CommRing_toNonUnitalCommRing___redArg(x_7);
x_9 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_8);
lean_inc_ref(x_9);
x_10 = l_NonUnitalNonAssocSemiring_toDistrib___redArg(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_HC4_doublingGradientMap___redArg___lam__0), 7, 6);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_11);
x_16 = lean_apply_1(x_2, x_13);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
lean_inc(x_17);
x_19 = lean_alloc_closure((void*)(l_HC4_doublingGradientMap___redArg___lam__0), 7, 6);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_9);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_11);
x_20 = lean_apply_1(x_2, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_HC4_doublingGradientMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_doublingGradientMap___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_PlanarJC2Interface(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_NonsingularInverse(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_PlanarDoublingInjectivity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_PlanarJC2Interface(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_NonsingularInverse(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_doublingGradientMap___redArg___lam__0___closed__0 = _init_l_HC4_doublingGradientMap___redArg___lam__0___closed__0();
lean_mark_persistent(l_HC4_doublingGradientMap___redArg___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
