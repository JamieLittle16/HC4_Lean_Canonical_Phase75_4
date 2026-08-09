// Lean compiler output
// Module: HC4.Polynomial
// Imports: Init HC4.Polynomial.WeightedInitial HC4.Polynomial.DerivativeWeight HC4.Polynomial.DeterminantWeight HC4.Polynomial.HessianDeterminant HC4.Polynomial.WeightBounds HC4.Polynomial.DerivativeBounds HC4.Polynomial.TopProduct HC4.Polynomial.MaximalHessianInitial HC4.Polynomial.FourExponent HC4.Polynomial.MonomialHessian HC4.Polynomial.RankThreePencils HC4.Polynomial.RankThreeLinearCoefficient HC4.Polynomial.AutonomousODEReconstruction HC4.Polynomial.RankThreeLogHessian HC4.Polynomial.ComplementaryLogHessian HC4.Polynomial.LogarithmicInitialSlope HC4.Polynomial.ComplementaryEdgeAssembly HC4.Polynomial.ComplementaryFractionBridge HC4.Polynomial.LogHessianMoments HC4.Polynomial.ComplementaryMvSubstitution HC4.Polynomial.ComplementaryMvMomentRealisation HC4.Polynomial.ComplementaryEdgeRigidity HC4.Polynomial.AutonomousODEQuadraticRigidity HC4.Polynomial.AutonomousODEPoleOrder HC4.Polynomial.AutonomousODEPolynomialDegree HC4.Polynomial.AutonomousODETranslation HC4.Polynomial.RankThreeFractionBridge
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
lean_object* initialize_HC4_Polynomial_WeightedInitial(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_DerivativeWeight(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_DeterminantWeight(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_HessianDeterminant(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_WeightBounds(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_DerivativeBounds(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_TopProduct(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_MaximalHessianInitial(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_FourExponent(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_MonomialHessian(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_RankThreePencils(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_RankThreeLinearCoefficient(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_AutonomousODEReconstruction(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_RankThreeLogHessian(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryLogHessian(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_LogarithmicInitialSlope(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryEdgeAssembly(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryFractionBridge(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_LogHessianMoments(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryMvSubstitution(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryMvMomentRealisation(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_ComplementaryEdgeRigidity(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_AutonomousODEQuadraticRigidity(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_AutonomousODEPoleOrder(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_AutonomousODEPolynomialDegree(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_AutonomousODETranslation(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_RankThreeFractionBridge(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Polynomial(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_WeightedInitial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_DerivativeWeight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_DeterminantWeight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_HessianDeterminant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_WeightBounds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_DerivativeBounds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_TopProduct(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_MaximalHessianInitial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_FourExponent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_MonomialHessian(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_RankThreePencils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_RankThreeLinearCoefficient(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_AutonomousODEReconstruction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_RankThreeLogHessian(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryLogHessian(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_LogarithmicInitialSlope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryEdgeAssembly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryFractionBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_LogHessianMoments(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryMvSubstitution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryMvMomentRealisation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_ComplementaryEdgeRigidity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_AutonomousODEQuadraticRigidity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_AutonomousODEPoleOrder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_AutonomousODEPolynomialDegree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_AutonomousODETranslation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_RankThreeFractionBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
