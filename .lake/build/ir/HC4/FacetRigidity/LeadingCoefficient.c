// Lean compiler output
// Module: HC4.FacetRigidity.LeadingCoefficient
// Imports: Init Mathlib
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
LEAN_EXPORT lean_object* l_HC4_FacetRigidity_facetLeadingFactor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_FacetRigidity_facetLeadingFactor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_FacetRigidity_facetLeadingFactor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_4, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_nat_mul(x_2, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_mul(x_9, x_2);
x_11 = lean_nat_sub(x_10, x_6);
lean_dec(x_10);
x_12 = lean_nat_mul(x_1, x_11);
lean_dec(x_11);
x_13 = lean_nat_mul(x_12, x_3);
lean_dec(x_12);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_13);
lean_dec(x_8);
x_15 = lean_nat_pow(x_1, x_4);
x_16 = lean_nat_pow(x_3, x_4);
x_17 = lean_nat_mul(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_nat_add(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_HC4_FacetRigidity_facetLeadingFactor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_FacetRigidity_facetLeadingFactor(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_FacetRigidity_LeadingCoefficient(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
