// Lean compiler output
// Module: HC4.Newton.TerminalConformalWeight
// Imports: Init HC4.Newton.MixedDepartureAdapter Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0(lean_object*);
lean_object* l_Multiset_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_integralWeightedDegree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_integralWeightedDegree___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_integralWeightedDegree___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___lam__0___boxed), 2, 0);
x_3 = l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___closed__0;
x_4 = l_List_foldrTR___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___redArg(x_2, x_1);
x_4 = l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_alloc_closure((void*)(l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_integralWeightedDegree___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_nat_to_int(x_3);
x_5 = lean_apply_1(x_1, x_2);
x_6 = lean_int_mul(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_integralWeightedDegree___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_HC4_Newton_integralWeightedDegree___redArg___lam__0), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_integralWeightedDegree(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_integralWeightedDegree___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_to_int(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_HC4_Newton_integralOrdinaryDegree___redArg___lam__0___boxed), 2, 0);
x_3 = l_Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_integralOrdinaryDegree___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_integralOrdinaryDegree___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_integralOrdinaryDegree___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_MixedDepartureAdapter(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_TerminalConformalWeight(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_MixedDepartureAdapter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___closed__0 = _init_l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Multiset_sum___at___Finset_sum___at___Finsupp_sum___at___HC4_Newton_integralWeightedDegree_spec__0_spec__0_spec__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
