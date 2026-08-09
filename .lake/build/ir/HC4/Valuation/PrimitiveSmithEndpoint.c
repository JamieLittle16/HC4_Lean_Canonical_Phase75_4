// Lean compiler output
// Module: HC4.Valuation.PrimitiveSmithEndpoint
// Imports: Init HC4.Valuation.AlignedSmithEndpoint Mathlib.Algebra.Polynomial.Expand Mathlib.RingTheory.MvPolynomial.Homogeneous Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Valuation_noWallPrimitiveSmithStep(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_noWallPrimitiveSmithStep___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_noWallPrimitiveSmithStep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_noWallPrimitiveSmithStep___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Valuation_noWallPrimitiveSmithStep(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AlignedSmithEndpoint(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Expand(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_RingTheory_MvPolynomial_Homogeneous(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_PrimitiveSmithEndpoint(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AlignedSmithEndpoint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Expand(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_RingTheory_MvPolynomial_Homogeneous(builtin, lean_io_mk_world());
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
