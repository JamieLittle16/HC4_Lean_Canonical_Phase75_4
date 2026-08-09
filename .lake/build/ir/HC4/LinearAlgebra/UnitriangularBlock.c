// Lean compiler output
// Module: HC4.LinearAlgebra.UnitriangularBlock
// Imports: Init HC4.MongeAmpere.SchurReduction
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
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_upperBlockUnitriangular(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_Matrix_fromBlocks___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_upperBlockUnitriangular___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_diagonal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_1);
x_7 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_8 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_7);
x_9 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_14, 0, x_10);
x_15 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc_ref(x_15);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Matrix_diagonal), 7, 5);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_10);
lean_closure_set(x_16, 4, x_15);
x_17 = lean_alloc_closure((void*)(l_Matrix_diagonal), 7, 5);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, lean_box(0));
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_10);
lean_closure_set(x_17, 4, x_15);
x_18 = l_Matrix_fromBlocks___redArg(x_16, x_14, x_4, x_17, x_5, x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_upperBlockUnitriangular___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_1);
x_7 = l_CommRing_toNonUnitalCommRing___redArg(x_1);
x_8 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_7);
x_9 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Ring_toAddGroupWithOne___redArg(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_14, 0, x_10);
x_15 = lean_alloc_closure((void*)(l_HC4_LinearAlgebra_lowerBlockUnitriangular___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc_ref(x_15);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Matrix_diagonal), 7, 5);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_10);
lean_closure_set(x_16, 4, x_15);
x_17 = lean_alloc_closure((void*)(l_Matrix_diagonal), 7, 5);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, lean_box(0));
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_10);
lean_closure_set(x_17, 4, x_15);
x_18 = l_Matrix_fromBlocks___redArg(x_16, x_4, x_14, x_17, x_5, x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_HC4_LinearAlgebra_upperBlockUnitriangular(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_HC4_LinearAlgebra_upperBlockUnitriangular___redArg(x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_MongeAmpere_SchurReduction(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_LinearAlgebra_UnitriangularBlock(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_SchurReduction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
