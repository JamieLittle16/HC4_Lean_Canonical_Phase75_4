// Lean compiler output
// Module: HC4.RationalRigidity.LogarithmicInfinityCertificate
// Imports: Init HC4.RationalRigidity.RankThreeReducedTarget HC4.Polynomial.AutonomousODEQuadraticRigidity Mathlib.FieldTheory.RatFunc.Degree Mathlib.Algebra.Polynomial.Degree.Lemmas Mathlib.Algebra.Polynomial.Degree.Monomial Mathlib.Tactic
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_RankThreeReducedTarget(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_AutonomousODEQuadraticRigidity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_FieldTheory_RatFunc_Degree(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Degree_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Polynomial_Degree_Monomial(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_RationalRigidity_LogarithmicInfinityCertificate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_RankThreeReducedTarget(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_AutonomousODEQuadraticRigidity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_FieldTheory_RatFunc_Degree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Degree_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Polynomial_Degree_Monomial(builtin, lean_io_mk_world());
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
