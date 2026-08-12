import HC4.Valuation.AdaptiveAlignedSmithExactSchurClock
import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# Adaptive exact four-block Schur data

The matrix-level adaptive Schur clock is already enough to exhaust the
preterminal branch.  What remains is to obtain such a clock from the honest
`2+2` Hessian block of the retained aligned family.

This file is the adaptive, frontier-free analogue of
`FrontierExactFourBlockSchurData`.

It deliberately contains no blocker-specific assertion.  Its fields are
exactly the concrete facts which a blocker extraction theorem must prove:

* an actual symmetric `2+2` polynomial Hessian block;
* its full determinant is the endpoint's exact closing monomial;
* the active determinant is a unit at the special parameter;
* the constant cleared binary Schur block has one of the two rank-one pivot
  forms already supported by `RankOneSchurSeriesAlignment`.

Once those facts are supplied, this file constructs the
`AdaptiveAlignedExactRankOneSchurClock` and hence obtains the complete
preterminal-rank-two / determinant-closing dichotomy automatically.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- Exact four-block data over a genuine adaptive aligned endpoint.

This is intentionally indexed directly by the endpoint, not by the legacy
homogeneous `CanonicalSmithDepartureFrontier`.
-/
structure AdaptiveAlignedExactFourBlockSchurData
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) where
  block :
    GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K))
  fullDet :
    block.determinantCore = Polynomial.X ^ E.defect
  activeDet_coeff_zero_ne_zero :
    block.activeDet.coeff 0 ≠ 0
  rigid :
    block.polynomialSchurSeries.LeftPivot ∨
      block.polynomialSchurSeries.RightAxisPivot

namespace AdaptiveAlignedExactFourBlockSchurData

/-- Left-pivot adaptive four-block data produces the exact adaptive matrix
Schur clock. -/
noncomputable def toClockLeft
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (B : AdaptiveAlignedExactFourBlockSchurData E)
    (hleft : B.block.polynomialSchurSeries.LeftPivot) :
    AdaptiveAlignedExactRankOneSchurClock E where
  series := B.block.polynomialSchurSeries.alignLeft hleft
  leading_ne_zero :=
    B.block.polynomialSchurSeries.alignLeft_leading_ne_zero hleft
  clearedFactor :=
    (Polynomial.C
      (B.block.polynomialSchurSeries.active.coeff 0)) ^ 2 *
      B.block.activeDet
  clearedFactor_coeff_zero_ne_zero := by
    have ha :
        B.block.polynomialSchurSeries.active.coeff 0 ≠ 0 :=
      hleft.1
    have hprod :
        (B.block.polynomialSchurSeries.active.coeff 0) ^ 2 *
            B.block.activeDet.coeff 0 ≠ 0 :=
      mul_ne_zero
        (pow_ne_zero 2 ha)
        B.activeDet_coeff_zero_ne_zero
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only
      [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hprod
  schurFactor := by
    calc
      (B.block.polynomialSchurSeries.alignLeft hleft).determinant =
          (Polynomial.C
            (B.block.polynomialSchurSeries.active.coeff 0)) ^ 2 *
            B.block.polynomialSchurSeries.determinant :=
        B.block.polynomialSchurSeries.alignLeft_determinant hleft
      _ =
          (Polynomial.C
            (B.block.polynomialSchurSeries.active.coeff 0)) ^ 2 *
            (B.block.activeDet * B.block.determinantCore) := by
        rw [B.block.polynomialSchurSeries_determinant]
      _ =
          ((Polynomial.C
            (B.block.polynomialSchurSeries.active.coeff 0)) ^ 2 *
            B.block.activeDet) *
              Polynomial.X ^ E.defect := by
        rw [B.fullDet]
        ring

/-- Right-axis adaptive four-block data produces the exact adaptive matrix
Schur clock. -/
noncomputable def toClockRight
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (B : AdaptiveAlignedExactFourBlockSchurData E)
    (hright : B.block.polynomialSchurSeries.RightAxisPivot) :
    AdaptiveAlignedExactRankOneSchurClock E where
  series := B.block.polynomialSchurSeries.alignRight hright
  leading_ne_zero :=
    B.block.polynomialSchurSeries.alignRight_leading_ne_zero hright
  clearedFactor := B.block.activeDet
  clearedFactor_coeff_zero_ne_zero :=
    B.activeDet_coeff_zero_ne_zero
  schurFactor := by
    calc
      (B.block.polynomialSchurSeries.alignRight hright).determinant =
          B.block.polynomialSchurSeries.determinant :=
        B.block.polynomialSchurSeries.alignRight_determinant hright
      _ = B.block.activeDet * B.block.determinantCore :=
        B.block.polynomialSchurSeries_determinant
      _ = B.block.activeDet * Polynomial.X ^ E.defect := by
        rw [B.fullDet]

/-- Every rigid adaptive four-block therefore produces an exact adaptive
rank-one Schur clock. -/
theorem exists_exactRankOneSchurClock
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (B : AdaptiveAlignedExactFourBlockSchurData E) :
    Nonempty (AdaptiveAlignedExactRankOneSchurClock E) := by
  rcases B.rigid with hleft | hright
  · exact ⟨B.toClockLeft hleft⟩
  · exact ⟨B.toClockRight hright⟩

/-- Complete adaptive four-block exhaustion: strict rank-two repair before
closure, or a genuinely transverse coefficient at the exact closing order. -/
theorem rankTwoProgress_or_closing
    {degreeCap complexity : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (B : AdaptiveAlignedExactFourBlockSchurData E) :
    (∃ S : AdaptiveAlignedExactRankOneSchurClock E,
      RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity) ∧
        S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
        (rankTwoRepairState complexity).measure <
          (rankOneRepairState complexity).measure) ∨
    (∃ S : AdaptiveAlignedExactRankOneSchurClock E,
      S.firstOrder = E.defect ∧
        (S.series.offDiag.coeff E.defect ≠ 0 ∨
         S.series.kernel.coeff E.defect ≠ 0)) := by
  rcases B.rigid with hleft | hright
  · let S := B.toClockLeft hleft
    rcases S.rankTwoProgress_or_closing
        (complexity := complexity) with hprogress | hclose
    · exact Or.inl ⟨S, hprogress⟩
    · exact Or.inr ⟨S, hclose⟩
  · let S := B.toClockRight hright
    rcases S.rankTwoProgress_or_closing
        (complexity := complexity) with hprogress | hclose
    · exact Or.inl ⟨S, hprogress⟩
    · exact Or.inr ⟨S, hclose⟩

end AdaptiveAlignedExactFourBlockSchurData

/-! ## Blocker-facing four-block target -/

/-- Precise four-block extraction target for a canonical aligned blocker.

Unlike the earlier Schur-clock certificate, this exposes exactly the finite
matrix facts which the blocker geometry must prove.
-/
def HasAdaptiveAlignedBlockerExactFourBlockSchurData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) : Prop :=
  Nonempty
    (AdaptiveAlignedExactFourBlockSchurData
      B.aligned.endpoint)

/-- Four-block extraction immediately yields the exact rank-one Schur clock
certificate used by the adaptive Schur exhaustion file. -/
theorem HasAdaptiveAlignedBlockerExactFourBlockSchurData.toExactSchurClock
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (h : HasAdaptiveAlignedBlockerExactFourBlockSchurData B) :
    HasAdaptiveAlignedBlockerExactSchurClock B := by
  rcases h with ⟨F⟩
  exact F.exists_exactRankOneSchurClock

/-- Consequently the blocker is fully reduced to the already-proved
preterminal/closing Schur dichotomy once its four-block extraction is
available. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rankTwoProgress_or_closing_of_exactFourBlock
    {degreeCap complexity : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (h : HasAdaptiveAlignedBlockerExactFourBlockSchurData B) :
    (∃ S : AdaptiveAlignedExactRankOneSchurClock B.aligned.endpoint,
      RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity) ∧
        S.series.offDiag.coeff S.firstOrder ≠ 0 ∧
        (rankTwoRepairState complexity).measure <
          (rankOneRepairState complexity).measure) ∨
    (∃ S : AdaptiveAlignedExactRankOneSchurClock B.aligned.endpoint,
      S.firstOrder = B.aligned.endpoint.defect ∧
        (S.series.offDiag.coeff B.aligned.endpoint.defect ≠ 0 ∨
         S.series.kernel.coeff B.aligned.endpoint.defect ≠ 0)) := by
  rcases h with ⟨F⟩
  exact F.rankTwoProgress_or_closing (complexity := complexity)

end

end HC4.Valuation
