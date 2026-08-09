// Lean compiler output
// Module: HC4.Valuation.SymmetricSmithImprovementRestart
// Imports: Init HC4.Newton.SymmetricSmithMinimality HC4.Valuation.CommonParameterFactorRestart Mathlib.Tactic
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
static lean_object* l_HC4_Valuation_smithAxisProjection___closed__1;
static lean_object* l_HC4_Valuation_smithAxisProjection___closed__0;
lean_object* l_HC4_Newton_smithSupportExponentOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_smithAxisProjection(lean_object*);
static lean_object* l_HC4_Valuation_smithAxisProjection___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* _init_l_HC4_Valuation_smithAxisProjection___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_smithAxisProjection___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Valuation_smithAxisProjection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_smithAxisProjection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_HC4_Valuation_smithAxisProjection___closed__0;
x_3 = l_HC4_Valuation_smithAxisProjection___closed__1;
x_4 = l_HC4_Valuation_smithAxisProjection___closed__2;
x_5 = l_HC4_Newton_smithSupportExponentOf___redArg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_SymmetricSmithMinimality(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_CommonParameterFactorRestart(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_SymmetricSmithImprovementRestart(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_SymmetricSmithMinimality(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_CommonParameterFactorRestart(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_smithAxisProjection___closed__0 = _init_l_HC4_Valuation_smithAxisProjection___closed__0();
lean_mark_persistent(l_HC4_Valuation_smithAxisProjection___closed__0);
l_HC4_Valuation_smithAxisProjection___closed__1 = _init_l_HC4_Valuation_smithAxisProjection___closed__1();
lean_mark_persistent(l_HC4_Valuation_smithAxisProjection___closed__1);
l_HC4_Valuation_smithAxisProjection___closed__2 = _init_l_HC4_Valuation_smithAxisProjection___closed__2();
lean_mark_persistent(l_HC4_Valuation_smithAxisProjection___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
