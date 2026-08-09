// Lean compiler output
// Module: HC4.Newton.TerminalCoordinatePermutation
// Imports: Init HC4.Newton.TerminalOneZeroEndpoint Mathlib.Algebra.MvPolynomial.Rename Mathlib.LinearAlgebra.Matrix.Reindex Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPermutePoint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Equiv_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPermutePoint___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPermutePoint___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Equiv_symm___redArg(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_1(x_5, x_3);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_terminalPermutePoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Newton_terminalPermutePoint___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalOneZeroEndpoint(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_MvPolynomial_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_LinearAlgebra_Matrix_Reindex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_TerminalCoordinatePermutation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalOneZeroEndpoint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_MvPolynomial_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_LinearAlgebra_Matrix_Reindex(builtin, lean_io_mk_world());
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
