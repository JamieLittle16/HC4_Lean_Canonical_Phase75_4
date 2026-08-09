import Mathlib

/-!
# First-departure binary Hessian source

This module isolates the elementary algebra used at the first preterminal
one-sided departure in the JC2 => HC4 restart spine.

If the departing coefficient has the form

  P_j(U,V;X) = V * A(U;X) + B(U;X),

then its binary Hessian in `(U,V)` has the schematic form

  [[*,   A_U],
   [A_U,   0 ]].

Consequently its binary determinant is `-(A_U)^2`.  Over a field this
vanishes exactly in the affine/separated branch `A_U = 0`; if `A_U != 0`
the determinant source is nonzero and is the mixed-pivot signal required by
the finite repair-termination interface.

The point of keeping this file scalar is that it can be imported by the
higher-level polynomial adapter without committing that adapter to a
particular matrix/Hessian representation.
-/

namespace HC4.Newton

/-- The determinant of the schematic binary Hessian
`[[hUU, aU], [aU, 0]]` occurring at a first affine-in-`V` departure. -/
def firstDepartureBinaryDet {R : Type*} [CommRing R] (hUU aU : R) : R :=
  hUU * 0 - aU * aU

@[simp]
theorem firstDepartureBinaryDet_eq_neg_sq
    {R : Type*} [CommRing R] (hUU aU : R) :
    firstDepartureBinaryDet hUU aU = -(aU ^ 2) := by
  simp [firstDepartureBinaryDet, pow_two]

/-- Over a field, the preterminal binary determinant vanishes exactly when
its mixed derivative `aU` vanishes. -/
@[simp]
theorem firstDepartureBinaryDet_eq_zero_iff
    {K : Type*} [Field K] (hUU aU : K) :
    firstDepartureBinaryDet hUU aU = 0 ↔ aU = 0 := by
  simp [firstDepartureBinaryDet_eq_neg_sq]

/-- A genuinely mixed first departure (`aU != 0`) supplies a nonzero binary
Hessian determinant source. -/
theorem firstDeparture_mixed_source_ne_zero
    {K : Type*} [Field K] (hUU aU : K) (haU : aU ≠ 0) :
    firstDepartureBinaryDet hUU aU ≠ 0 := by
  simpa using (not_congr (firstDepartureBinaryDet_eq_zero_iff hUU aU)).2 haU

/-- Exact algebraic dichotomy at a preterminal affine-in-`V` departure:
either the mixed derivative vanishes and the binary source is zero, or the
mixed derivative is nonzero and so is the source. -/
theorem firstDeparture_binary_source_dichotomy
    {K : Type*} [Field K] (hUU aU : K) :
    (aU = 0 ∧ firstDepartureBinaryDet hUU aU = 0) ∨
      (aU ≠ 0 ∧ firstDepartureBinaryDet hUU aU ≠ 0) := by
  by_cases haU : aU = 0
  · left
    exact ⟨haU, (firstDepartureBinaryDet_eq_zero_iff hUU aU).2 haU⟩
  · right
    exact ⟨haU, firstDeparture_mixed_source_ne_zero hUU aU haU⟩

/-- Characteristic-zero spelling of the mixed-source theorem, matching the
ambient hypothesis used by the restart formalisation. -/
theorem firstDeparture_mixed_source_ne_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (hUU aU : K) (haU : aU ≠ 0) :
    firstDepartureBinaryDet hUU aU ≠ 0 :=
  firstDeparture_mixed_source_ne_zero hUU aU haU

end HC4.Newton
