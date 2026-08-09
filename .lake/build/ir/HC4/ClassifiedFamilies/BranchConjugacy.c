// Lean compiler output
// Module: HC4.ClassifiedFamilies.BranchConjugacy
// Imports: Init HC4.ClassifiedFamilies.TriangularInverse
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
static lean_object* l_HC4_ClassifiedFamilies_reversePointEquiv___closed__0;
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_reversePointEquiv(lean_object*);
lean_object* l_HC4_ClassifiedFamilies_sGradientMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_ClassifiedFamilies_rGradientInverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sGradientEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_ClassifiedFamilies_sGradientInverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_reversePoint___redArg(lean_object*);
lean_object* l_HC4_ClassifiedFamilies_rGradientMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rGradientEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_reversePoint(lean_object*, lean_object*);
static lean_object* l_HC4_ClassifiedFamilies_reversePointEquiv___closed__1;
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rGradientEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sGradientEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_reversePoint___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_reversePoint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_ClassifiedFamilies_reversePoint___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_HC4_ClassifiedFamilies_reversePointEquiv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_HC4_ClassifiedFamilies_reversePoint), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_HC4_ClassifiedFamilies_reversePointEquiv___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_HC4_ClassifiedFamilies_reversePointEquiv___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_reversePointEquiv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_ClassifiedFamilies_reversePointEquiv___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rGradientEquiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_HC4_ClassifiedFamilies_rGradientMap), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
lean_closure_set(x_5, 4, x_4);
x_6 = lean_alloc_closure((void*)(l_HC4_ClassifiedFamilies_rGradientInverse), 6, 5);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_rGradientEquiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_ClassifiedFamilies_rGradientEquiv___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sGradientEquiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_HC4_ClassifiedFamilies_sGradientMap), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
lean_closure_set(x_5, 4, x_4);
x_6 = lean_alloc_closure((void*)(l_HC4_ClassifiedFamilies_sGradientInverse), 6, 5);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_sGradientEquiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_ClassifiedFamilies_sGradientEquiv___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_ClassifiedFamilies_TriangularInverse(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_ClassifiedFamilies_BranchConjugacy(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_ClassifiedFamilies_TriangularInverse(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_ClassifiedFamilies_reversePointEquiv___closed__0 = _init_l_HC4_ClassifiedFamilies_reversePointEquiv___closed__0();
lean_mark_persistent(l_HC4_ClassifiedFamilies_reversePointEquiv___closed__0);
l_HC4_ClassifiedFamilies_reversePointEquiv___closed__1 = _init_l_HC4_ClassifiedFamilies_reversePointEquiv___closed__1();
lean_mark_persistent(l_HC4_ClassifiedFamilies_reversePointEquiv___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
