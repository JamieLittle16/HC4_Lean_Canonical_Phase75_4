// Lean compiler output
// Module: HC4.Newton.ZeroSchurFirstEntryClock
// Imports: Init HC4.Newton.RankOneSchurSeriesAlignment HC4.Newton.RankOneRepairProgress Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurFourBlockData_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurClock_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ZeroSchurSeries_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ExactRankOneSchurClockAt_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ExactRankOneSchurClockAt_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ZeroSchurSeries_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurFourBlockData_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurClock_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HC4_Newton_ZeroSchurSeries_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_ZeroSchurSeries_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_ZeroSchurSeries_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurClock_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurClock_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_ExactZeroSchurClock_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_ExactRankOneSchurClockAt_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_ExactRankOneSchurClockAt_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_ExactRankOneSchurClockAt_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurFourBlockData_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
}
LEAN_EXPORT lean_object* l_HC4_Newton_ExactZeroSchurFourBlockData_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_HC4_Newton_ExactZeroSchurFourBlockData_ctorIdx(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RankOneSchurSeriesAlignment(uint8_t builtin, lean_object*);
lean_object* initialize_HC4_Newton_RankOneRepairProgress(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HC4_Newton_ZeroSchurFirstEntryClock(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RankOneSchurSeriesAlignment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HC4_Newton_RankOneRepairProgress(builtin, lean_io_mk_world());
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
