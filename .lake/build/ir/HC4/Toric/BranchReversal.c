// Lean compiler output
// Module: HC4.Toric.BranchReversal
// Imports: Init HC4.Toric.CharacterSupport
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
LEAN_EXPORT lean_object* l_HC4_Toric_reverseExponent(lean_object*);
static lean_object* l_HC4_Toric_reverseExponentEquiv___closed__1;
LEAN_EXPORT lean_object* l_HC4_Toric_reverseExponentEquiv;
static lean_object* l_HC4_Toric_reverseExponentEquiv___closed__0;
LEAN_EXPORT lean_object* l_HC4_Toric_reverseExponent(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
lean_ctor_set(x_1, 3, x_3);
lean_ctor_set(x_1, 2, x_4);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_7);
return x_11;
}
}
}
static lean_object* _init_l_HC4_Toric_reverseExponentEquiv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_HC4_Toric_reverseExponent), 1, 0);
return x_1;
}
}
static lean_object* _init_l_HC4_Toric_reverseExponentEquiv___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_Toric_reverseExponentEquiv___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Toric_reverseExponentEquiv() {
_start:
{
lean_object* x_1; 
x_1 = l_HC4_Toric_reverseExponentEquiv___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_CharacterSupport(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Toric_BranchReversal(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_CharacterSupport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Toric_reverseExponentEquiv___closed__0 = _init_l_HC4_Toric_reverseExponentEquiv___closed__0();
lean_mark_persistent(l_HC4_Toric_reverseExponentEquiv___closed__0);
l_HC4_Toric_reverseExponentEquiv___closed__1 = _init_l_HC4_Toric_reverseExponentEquiv___closed__1();
lean_mark_persistent(l_HC4_Toric_reverseExponentEquiv___closed__1);
l_HC4_Toric_reverseExponentEquiv = _init_l_HC4_Toric_reverseExponentEquiv();
lean_mark_persistent(l_HC4_Toric_reverseExponentEquiv);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
