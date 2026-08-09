// Lean compiler output
// Module: HC4.Newton.FirstSchurLayerLinearization
// Imports: Init HC4.Newton.PreterminalFirstDeparture Mathlib.Algebra.BigOperators.NatAntidiagonal Mathlib.Algebra.Polynomial.Coeff Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_RankOneSchurSeries_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_PreterminalSchurDepartureData_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_RankOneSchurSeries_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_PreterminalSchurDepartureData_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstRankOneSchurDeparture_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstRankOneSchurDeparture_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_FirstRankOneSchurDeparture_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_FirstRankOneSchurDeparture_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_FirstRankOneSchurDeparture_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankOneSchurSeries_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_RankOneSchurSeries_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_RankOneSchurSeries_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_PreterminalSchurDepartureData_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_PreterminalSchurDepartureData_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_PreterminalSchurDepartureData_ctorIdx(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_PreterminalFirstDeparture(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_NatAntidiagonal(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Coeff(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_FirstSchurLayerLinearization(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_PreterminalFirstDeparture(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_NatAntidiagonal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Coeff(builtin, lean_io_mk_world());
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
