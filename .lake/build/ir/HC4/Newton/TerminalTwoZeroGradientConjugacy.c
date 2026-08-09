// Lean compiler output
// Module: HC4.Newton.TerminalTwoZeroGradientConjugacy
// Imports: Init HC4.Newton.TerminalTwoZeroKellerReduction HC4.PlanarJacobianEvaluation HC4.PlanarDoublingInjectivity Mathlib.Tactic
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
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardBasePoint___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardSplitPoint___redArg(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairEmbedding___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardBasePoint(lean_object*, lean_object*, lean_object*);
static lean_object* l_HC4_Newton_standardPositivePairEmbedding___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_HC4_Newton_standardPositivePairEmbedding___closed__0;
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardSplitPoint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairEmbedding(lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_HC4_Newton_standardPositivePairEmbedding___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_HC4_Newton_standardPositivePairEmbedding___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairEmbedding(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = l_HC4_Newton_standardPositivePairEmbedding___closed__0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_HC4_Newton_standardPositivePairEmbedding___closed__1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardPositivePairEmbedding___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HC4_Newton_standardPositivePairEmbedding(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardBasePoint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardBasePoint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_HC4_Newton_standardPositivePairEmbedding(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_standardFibrePoint___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_standardFibrePoint___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardFibrePoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_standardFibrePoint(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardSplitPoint___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_HC4_Newton_standardBasePoint), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
x_3 = lean_alloc_closure((void*)(l_HC4_Newton_standardFibrePoint___boxed), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_standardSplitPoint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HC4_Newton_standardSplitPoint___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_HC4_Newton_TerminalTwoZeroGradientConjugacy_0__HC4_Newton_standardPlanarPairMap_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_TerminalTwoZeroKellerReduction(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_PlanarJacobianEvaluation(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_PlanarDoublingInjectivity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_TerminalTwoZeroGradientConjugacy(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_TerminalTwoZeroKellerReduction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_PlanarJacobianEvaluation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_PlanarDoublingInjectivity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_HC4_Newton_standardPositivePairEmbedding___closed__0 = _init_l_HC4_Newton_standardPositivePairEmbedding___closed__0();
lean_mark_persistent(l_HC4_Newton_standardPositivePairEmbedding___closed__0);
l_HC4_Newton_standardPositivePairEmbedding___closed__1 = _init_l_HC4_Newton_standardPositivePairEmbedding___closed__1();
lean_mark_persistent(l_HC4_Newton_standardPositivePairEmbedding___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
