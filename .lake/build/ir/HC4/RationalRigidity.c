// Lean compiler output
// Module: HC4.RationalRigidity
// Imports: Init HC4.RationalRigidity.DenominatorClearing HC4.RationalRigidity.Assembly HC4.RationalRigidity.PoleRemovalAssembly HC4.RationalRigidity.ReducedFractionAssembly HC4.RationalRigidity.ChartCertificates HC4.RationalRigidity.FinitePreimage HC4.RationalRigidity.AutonomousDenominatorRemoval HC4.RationalRigidity.CanonicalReducedFraction HC4.RationalRigidity.LogarithmicSourceRegularity HC4.RationalRigidity.RegularRatFuncEvaluation HC4.RationalRigidity.AutonomousRatFuncAssembly HC4.RationalRigidity.LogarithmicSourceRatFunc HC4.RationalRigidity.RankThreeReducedTarget HC4.RationalRigidity.LogarithmicInfinityCertificate HC4.RationalRigidity.ClearedInfinityEvaluation HC4.RationalRigidity.RankThreeInfinityAssembly
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
lean_object* initialize_HC4_RationalRigidity_DenominatorClearing(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_Assembly(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_PoleRemovalAssembly(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_ReducedFractionAssembly(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_ChartCertificates(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_FinitePreimage(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_AutonomousDenominatorRemoval(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_CanonicalReducedFraction(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_LogarithmicSourceRegularity(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_RegularRatFuncEvaluation(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_AutonomousRatFuncAssembly(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_LogarithmicSourceRatFunc(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_RankThreeReducedTarget(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_LogarithmicInfinityCertificate(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_ClearedInfinityEvaluation(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_RationalRigidity_RankThreeInfinityAssembly(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_RationalRigidity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_DenominatorClearing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_Assembly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_PoleRemovalAssembly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_ReducedFractionAssembly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_ChartCertificates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_FinitePreimage(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_AutonomousDenominatorRemoval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_CanonicalReducedFraction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_LogarithmicSourceRegularity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_RegularRatFuncEvaluation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_AutonomousRatFuncAssembly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_LogarithmicSourceRatFunc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_RankThreeReducedTarget(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_LogarithmicInfinityCertificate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_ClearedInfinityEvaluation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_RationalRigidity_RankThreeInfinityAssembly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
