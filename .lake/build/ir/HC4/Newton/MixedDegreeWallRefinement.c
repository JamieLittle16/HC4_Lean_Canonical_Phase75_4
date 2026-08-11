// Lean compiler output
// Module: HC4.Newton.MixedDegreeWallRefinement
// Imports: Init HC4.Newton.MixedDegreeFirstWallCompetition HC4.Newton.RankOneRepairProgress HC4.Newton.TerminalTwoZeroSupport HC4.Polynomial.WeightedInitial HC4.Polynomial.MaximalHessianInitial HC4.Valuation.NonlinearDegreeBoundPreservation
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
LEAN_EXPORT lean_object* l_HC4_Newton_longitudinalIntegerWeight(lean_object*);
static lean_object* l_HC4_Newton_longitudinalIntegerWeight___closed__0;
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_HC4_Newton_longitudinalIntegerWeight___closed__2;
static lean_object* l_HC4_Newton_longitudinalIntegerWeight___closed__1;
LEAN_EXPORT lean_object* l_HC4_Newton_longitudinalIntegerWeight___boxed(lean_object*);
static lean_object* _init_l_HC4_Newton_longitudinalIntegerWeight___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Newton_longitudinalIntegerWeight___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_HC4_Newton_longitudinalIntegerWeight___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_longitudinalIntegerWeight(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_HC4_Newton_longitudinalIntegerWeight___closed__0;
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_HC4_Newton_longitudinalIntegerWeight___closed__1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_HC4_Newton_longitudinalIntegerWeight___closed__2;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_longitudinalIntegerWeight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_longitudinalIntegerWeight(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_MixedDegreeFirstWallCompetition(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RankOneRepairProgress(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalTwoZeroSupport(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_WeightedInitial(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Polynomial_MaximalHessianInitial(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_NonlinearDegreeBoundPreservation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_MixedDegreeWallRefinement(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_MixedDegreeFirstWallCompetition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RankOneRepairProgress(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalTwoZeroSupport(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_WeightedInitial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Polynomial_MaximalHessianInitial(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_NonlinearDegreeBoundPreservation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_longitudinalIntegerWeight___closed__0 = _init_l_HC4_Newton_longitudinalIntegerWeight___closed__0();
lean_mark_persistent(l_HC4_Newton_longitudinalIntegerWeight___closed__0);
l_HC4_Newton_longitudinalIntegerWeight___closed__1 = _init_l_HC4_Newton_longitudinalIntegerWeight___closed__1();
lean_mark_persistent(l_HC4_Newton_longitudinalIntegerWeight___closed__1);
l_HC4_Newton_longitudinalIntegerWeight___closed__2 = _init_l_HC4_Newton_longitudinalIntegerWeight___closed__2();
lean_mark_persistent(l_HC4_Newton_longitudinalIntegerWeight___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
