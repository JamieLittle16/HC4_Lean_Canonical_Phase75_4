// Lean compiler output
// Module: HC4.Valuation.AdaptiveSectionBoundaryNormalization
// Imports: Init HC4.Valuation.AdaptiveAlignedSmithExposureGeometry Mathlib.Tactic
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
static lean_object* l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg___closed__0;
lean_object* l_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_pointedBoundaryShearCoefficient(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HC4_Valuation_polynomialSectionSpecialPoint___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toEuclideanDomain___redArg(lean_object*);
static lean_object* _init_l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg___closed__0;
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = l_HC4_Valuation_polynomialSectionSpecialPoint___redArg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = l_Field_toEuclideanDomain___redArg(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = l_CommRing_toNonUnitalCommRing___redArg(x_8);
x_10 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___redArg(x_9);
x_11 = l_NonUnitalNonAssocSemiring_toMulZeroClass___redArg(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Valuation_pointedBoundaryShearCoefficient(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Valuation_AdaptiveAlignedSmithExposureGeometry(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Valuation_AdaptiveSectionBoundaryNormalization(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Valuation_AdaptiveAlignedSmithExposureGeometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg___closed__0 = _init_l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg___closed__0();
lean_mark_persistent(l_HC4_Valuation_pointedBoundaryShearCoefficient___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
