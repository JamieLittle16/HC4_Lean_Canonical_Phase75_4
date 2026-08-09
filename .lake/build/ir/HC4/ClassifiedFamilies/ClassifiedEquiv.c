// Lean compiler output
// Module: HC4.ClassifiedFamilies.ClassifiedEquiv
// Imports: Init HC4.ClassifiedFamilies.BranchConjugacy
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
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradient___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradient(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___redArg(lean_object*);
lean_object* l_HC4_ClassifiedFamilies_sGradientInverse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_r_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_s_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_r_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_s_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_ClassifiedFamilies_sGradientMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_ClassifiedFamilies_rGradientInverse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradientEquiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_ClassifiedFamilies_rGradientMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradientEquiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedInverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedInverse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_r_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_r_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_s_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_ClassifiedBranch_s_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_ClassifiedFamilies_ClassifiedBranch_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradient___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_HC4_ClassifiedFamilies_rGradientMap___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = l_HC4_ClassifiedFamilies_sGradientMap___redArg(x_1, x_2, x_3, x_8, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradient(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_classifiedGradient___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedInverse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_HC4_ClassifiedFamilies_rGradientInverse___redArg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = l_HC4_ClassifiedFamilies_sGradientInverse___redArg(x_1, x_2, x_3, x_8, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedInverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_HC4_ClassifiedFamilies_classifiedInverse___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradientEquiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_HC4_ClassifiedFamilies_classifiedGradient), 6, 5);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_2);
lean_closure_set(x_5, 3, x_3);
lean_closure_set(x_5, 4, x_4);
x_6 = lean_alloc_closure((void*)(l_HC4_ClassifiedFamilies_classifiedInverse), 6, 5);
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
LEAN_EXPORT lean_object* l_HC4_ClassifiedFamilies_classifiedGradientEquiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_ClassifiedFamilies_classifiedGradientEquiv___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_ClassifiedFamilies_BranchConjugacy(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_ClassifiedFamilies_ClassifiedEquiv(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_ClassifiedFamilies_BranchConjugacy(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
