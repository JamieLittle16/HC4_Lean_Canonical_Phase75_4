// Lean compiler output
// Module: HC4.Newton.OneZeroBlockDeterminant
// Imports: Init Mathlib.LinearAlgebra.Matrix.Determinant.Basic Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroHessianBlockMatrix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
static lean_object* l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__0;
lean_object* l_Equiv_refl(lean_object*);
static lean_object* l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__1;
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroHessianBlockMatrix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Equiv_refl(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroHessianBlockMatrix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_15 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_16 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_15);
x_17 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__0;
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__1;
x_26 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_5);
lean_closure_set(x_26, 3, x_25);
x_27 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_23);
lean_closure_set(x_27, 2, x_4);
lean_closure_set(x_27, 3, x_26);
x_28 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_28, 0, lean_box(0));
lean_closure_set(x_28, 1, x_22);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_27);
x_29 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_29, 0, lean_box(0));
lean_closure_set(x_29, 1, x_21);
lean_closure_set(x_29, 2, x_2);
lean_closure_set(x_29, 3, x_28);
lean_inc(x_18);
x_30 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, x_24);
lean_closure_set(x_30, 2, x_18);
lean_closure_set(x_30, 3, x_25);
lean_inc(x_18);
x_31 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, x_23);
lean_closure_set(x_31, 2, x_18);
lean_closure_set(x_31, 3, x_30);
lean_inc(x_18);
x_32 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, x_22);
lean_closure_set(x_32, 2, x_18);
lean_closure_set(x_32, 3, x_31);
x_33 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_33, 0, lean_box(0));
lean_closure_set(x_33, 1, x_21);
lean_closure_set(x_33, 2, x_6);
lean_closure_set(x_33, 3, x_32);
x_34 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, x_24);
lean_closure_set(x_34, 2, x_9);
lean_closure_set(x_34, 3, x_25);
x_35 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_35, 0, lean_box(0));
lean_closure_set(x_35, 1, x_23);
lean_closure_set(x_35, 2, x_8);
lean_closure_set(x_35, 3, x_34);
lean_inc(x_18);
x_36 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_36, 0, lean_box(0));
lean_closure_set(x_36, 1, x_22);
lean_closure_set(x_36, 2, x_18);
lean_closure_set(x_36, 3, x_35);
x_37 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, x_21);
lean_closure_set(x_37, 2, x_7);
lean_closure_set(x_37, 3, x_36);
x_38 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_38, 0, lean_box(0));
lean_closure_set(x_38, 1, x_24);
lean_closure_set(x_38, 2, x_12);
lean_closure_set(x_38, 3, x_25);
x_39 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_39, 0, lean_box(0));
lean_closure_set(x_39, 1, x_23);
lean_closure_set(x_39, 2, x_11);
lean_closure_set(x_39, 3, x_38);
x_40 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, x_22);
lean_closure_set(x_40, 2, x_18);
lean_closure_set(x_40, 3, x_39);
x_41 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, x_21);
lean_closure_set(x_41, 2, x_10);
lean_closure_set(x_41, 3, x_40);
x_42 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_42, 0, lean_box(0));
lean_closure_set(x_42, 1, x_24);
lean_closure_set(x_42, 2, x_41);
lean_closure_set(x_42, 3, x_25);
x_43 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_43, 0, lean_box(0));
lean_closure_set(x_43, 1, x_23);
lean_closure_set(x_43, 2, x_37);
lean_closure_set(x_43, 3, x_42);
x_44 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_44, 0, lean_box(0));
lean_closure_set(x_44, 1, x_22);
lean_closure_set(x_44, 2, x_33);
lean_closure_set(x_44, 3, x_43);
x_45 = lean_alloc_closure((void*)(l_Matrix_vecCons___boxed), 5, 4);
lean_closure_set(x_45, 0, lean_box(0));
lean_closure_set(x_45, 1, x_21);
lean_closure_set(x_45, 2, x_29);
lean_closure_set(x_45, 3, x_44);
x_46 = lean_apply_3(x_20, x_45, x_13, x_14);
return x_46;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_oneZeroHessianBlockMatrix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_HC4_Newton_oneZeroHessianBlockMatrix___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_OneZeroBlockDeterminant(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Determinant_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__0 = _init_l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__0();
lean_mark_persistent(l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__0);
l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__1 = _init_l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__1();
lean_mark_persistent(l_HC4_Newton_oneZeroHessianBlockMatrix___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
