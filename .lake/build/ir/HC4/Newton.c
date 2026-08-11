// Lean compiler output
// Module: HC4.Newton
// Imports: Init HC4.Newton.ExposedFaces HC4.Newton.Equivariance HC4.Newton.FirstContactArithmetic HC4.Newton.ScaledContact HC4.Newton.BoundaryCycle HC4.Newton.FirstContactSelection HC4.Newton.FirstNonfacetContact HC4.Newton.InteriorVertex HC4.Newton.FacetCycleClassification HC4.Newton.FourBoundaryCycle HC4.Newton.FirstNonfacetBoundary HC4.Newton.BoundaryStrata HC4.Newton.ComplementaryEdgeArithmetic HC4.Newton.RestartClassification HC4.Newton.GlobalRestartClassification HC4.Newton.AdaptiveRestartClassification HC4.Newton.MixedDegreeAxisCollision HC4.Newton.MixedDegreeFirstWallCompetition HC4.Newton.MixedDegreeWallRefinement HC4.Newton.AdaptivePacketExposure
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
lean_object* initialize_HC4_Newton_ExposedFaces(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_Equivariance(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FirstContactArithmetic(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_ScaledContact(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_BoundaryCycle(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FirstContactSelection(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FirstNonfacetContact(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_InteriorVertex(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FacetCycleClassification(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FourBoundaryCycle(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_FirstNonfacetBoundary(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_BoundaryStrata(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_ComplementaryEdgeArithmetic(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RestartClassification(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_GlobalRestartClassification(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_AdaptiveRestartClassification(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_MixedDegreeAxisCollision(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_MixedDegreeFirstWallCompetition(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_MixedDegreeWallRefinement(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_AdaptivePacketExposure(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_ExposedFaces(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_Equivariance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FirstContactArithmetic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_ScaledContact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_BoundaryCycle(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FirstContactSelection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FirstNonfacetContact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_InteriorVertex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FacetCycleClassification(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FourBoundaryCycle(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_FirstNonfacetBoundary(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_BoundaryStrata(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_ComplementaryEdgeArithmetic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RestartClassification(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_GlobalRestartClassification(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_AdaptiveRestartClassification(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_MixedDegreeAxisCollision(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_MixedDegreeFirstWallCompetition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_MixedDegreeWallRefinement(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_AdaptivePacketExposure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
