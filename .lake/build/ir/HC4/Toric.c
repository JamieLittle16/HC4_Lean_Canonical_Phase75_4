// Lean compiler output
// Module: HC4.Toric
// Imports: Init HC4.Toric.InvariantSemigroup HC4.Toric.BranchCharacter HC4.Toric.CharacterSupport HC4.Toric.SparseEigenSupport HC4.Toric.SupportIntersection HC4.Toric.BranchReversal HC4.Toric.BranchCoordinates HC4.Toric.SymmetricEigenSupport HC4.Toric.Facets HC4.Toric.ExceptionalGrading HC4.Toric.CoefficientDescent HC4.Toric.ClassifiedSupport HC4.Toric.ClassifiedDescent HC4.Toric.BoundaryGeometry HC4.Toric.FourSidedCharacter
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
lean_object* initialize_HC4_Toric_InvariantSemigroup(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_BranchCharacter(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_CharacterSupport(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_SparseEigenSupport(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_SupportIntersection(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_BranchReversal(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_BranchCoordinates(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_SymmetricEigenSupport(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_Facets(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_ExceptionalGrading(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_CoefficientDescent(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_ClassifiedSupport(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_ClassifiedDescent(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_BoundaryGeometry(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Toric_FourSidedCharacter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Toric(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_InvariantSemigroup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_BranchCharacter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_CharacterSupport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_SparseEigenSupport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_SupportIntersection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_BranchReversal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_BranchCoordinates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_SymmetricEigenSupport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_Facets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_ExceptionalGrading(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_CoefficientDescent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_ClassifiedSupport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_ClassifiedDescent(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_BoundaryGeometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Toric_FourSidedCharacter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
