// Lean compiler output
// Module: HC4.Valuation.FinalRestartAssembly
// Imports: Init HC4.Valuation.SeparatedRightWallScaleDescent HC4.Newton.RestartClassification Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_CanonicalExactCollisionEntry_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HC4_Valuation_CanonicalExactCollisionEntry_toRestartState(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_SeparatedRightWallScaleDescent(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RestartClassification(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_FinalRestartAssembly(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_SeparatedRightWallScaleDescent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RestartClassification(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
