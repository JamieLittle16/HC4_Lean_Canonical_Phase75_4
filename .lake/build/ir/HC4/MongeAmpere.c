// Lean compiler output
// Module: HC4.MongeAmpere
// Imports: Init HC4.MongeAmpere.SchurReduction HC4.MongeAmpere.HyperbolicBase HC4.MongeAmpere.PolynomialInitial HC4.MongeAmpere.InitialFormBridge HC4.MongeAmpere.MaximalInitial HC4.MongeAmpere.FirstContactMaximal
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
lean_object* initialize_HC4_MongeAmpere_SchurReduction(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_MongeAmpere_HyperbolicBase(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_MongeAmpere_PolynomialInitial(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_MongeAmpere_InitialFormBridge(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_MongeAmpere_MaximalInitial(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_MongeAmpere_FirstContactMaximal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_MongeAmpere(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_SchurReduction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_HyperbolicBase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_PolynomialInitial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_InitialFormBridge(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_MaximalInitial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_MongeAmpere_FirstContactMaximal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
