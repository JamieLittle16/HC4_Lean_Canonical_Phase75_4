// Lean compiler output
// Module: HC4.Toric.BranchCoordinates
// Imports: Init HC4.Toric.SupportIntersection
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
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_sProjectedSupport___redArg(lean_object*);
LEAN_EXPORT uint8_t l_HC4_Toric_rProjectedSupport___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_HC4_Toric_sProjectedSupport___redArg___closed__1;
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_sCoordinates___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_sCoordinates(lean_object*);
static lean_object* l_HC4_Toric_sProjectedSupport___redArg___closed__0;
LEAN_EXPORT lean_object* l_HC4_Toric_rCoordinates(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_rCoordinates___boxed(lean_object*);
static lean_object* l_HC4_Toric_rProjectedSupport___redArg___closed__0;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_sProjectedSupport(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_sProjectedSupport___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Toric_rCoordinates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_rCoordinates___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Toric_rCoordinates(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_sCoordinates(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_sCoordinates___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Toric_sCoordinates(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_HC4_Toric_rProjectedSupport___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(x_3);
x_4 = l_instDecidableEqProd___redArg(x_3, x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_HC4_Toric_rProjectedSupport___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_HC4_Toric_rCoordinates___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_HC4_Toric_rProjectedSupport___redArg___lam__0___boxed), 2, 0);
x_4 = l_HC4_Toric_rProjectedSupport___redArg___closed__0;
x_5 = l_Finset_image___redArg(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Toric_rProjectedSupport___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HC4_Toric_rProjectedSupport___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_rProjectedSupport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Toric_rProjectedSupport(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_HC4_Toric_sProjectedSupport___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_HC4_Toric_rProjectedSupport___redArg___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_HC4_Toric_sProjectedSupport___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_HC4_Toric_sCoordinates___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_sProjectedSupport___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_HC4_Toric_sProjectedSupport___redArg___closed__0;
x_4 = l_HC4_Toric_sProjectedSupport___redArg___closed__1;
x_5 = l_Finset_image___redArg(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_sProjectedSupport(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Toric_sProjectedSupport___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Toric_sProjectedSupport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Toric_sProjectedSupport(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_SupportIntersection(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Toric_BranchCoordinates(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_SupportIntersection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Toric_rProjectedSupport___redArg___closed__0 = _init_l_HC4_Toric_rProjectedSupport___redArg___closed__0();
lean_mark_persistent(l_HC4_Toric_rProjectedSupport___redArg___closed__0);
l_HC4_Toric_sProjectedSupport___redArg___closed__0 = _init_l_HC4_Toric_sProjectedSupport___redArg___closed__0();
lean_mark_persistent(l_HC4_Toric_sProjectedSupport___redArg___closed__0);
l_HC4_Toric_sProjectedSupport___redArg___closed__1 = _init_l_HC4_Toric_sProjectedSupport___redArg___closed__1();
lean_mark_persistent(l_HC4_Toric_sProjectedSupport___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
