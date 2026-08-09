// Lean compiler output
// Module: HC4.Toric.ClassifiedSupport
// Imports: Init HC4.Toric.CoefficientDescent HC4.Toric.SupportIntersection
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
LEAN_EXPORT lean_object* l_HC4_Toric_zeroExponent;
static lean_object* l_HC4_Toric_zeroExponent___closed__0;
static lean_object* _init_l_HC4_Toric_zeroExponent___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Toric_zeroExponent() {
_start:
{
lean_object* x_1; 
x_1 = l_HC4_Toric_zeroExponent___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_CoefficientDescent(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_SupportIntersection(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Toric_ClassifiedSupport(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_CoefficientDescent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_SupportIntersection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Toric_zeroExponent___closed__0 = _init_l_HC4_Toric_zeroExponent___closed__0();
lean_mark_persistent(l_HC4_Toric_zeroExponent___closed__0);
l_HC4_Toric_zeroExponent = _init_l_HC4_Toric_zeroExponent();
lean_mark_persistent(l_HC4_Toric_zeroExponent);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
