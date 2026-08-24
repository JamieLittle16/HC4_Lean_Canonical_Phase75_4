import HC4.Valuation.AdaptiveAlignedSmithCanonicalScaleAwareHessianRankSplit
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectRankTwoGeometry
import Mathlib.Tactic

/-!
# A18.4.104: zero raw defect already carries complete rank-three geometry

Raw defect zero is the unit Hessian-determinant situation.  It is therefore
not a terminal exception to the finite-rank geometry.

A18.4.89 gives the honest finite split for the special-fibre Hessian of any
scale-aware state: either an exact active `2 x 2` chart is present, or every
`2 x 2` minor vanishes.  In the second branch four of those minors force the
full symmetric four-block determinant to vanish.  At raw defect zero the
constant coefficient of the exact Hessian clock is `1`, contradiction.

Thus every zero-defect state has an honest exact active chart, and A18.4.88
immediately supplies complete rank-three geometry on that same state.  No
repair-only promotion is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- At raw defect zero the special-fibre Hessian four-block has determinant
exactly one. -/
theorem ScaleAwareAdaptiveGeometricRestartState.zeroDefect_specialHessianDet_one
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    (scaleAwareSpecialHessianFourBlock s).determinantCore = 1 := by
  have hfull :=
    scaleAwareHessianFourBlock_determinantCore
      (Equiv.refl (Fin 4)) s
  have hcoeff := congrArg
    (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hfull
  simpa [scaleAwareSpecialHessianFourBlock,
    parameterConstantCoeffFourBlock,
    GeneralFourBlock.determinantCore,
    hzero, Polynomial.coeff_zero_eq_eval_zero] using hcoeff

/-- **Zero defect forces an honest active `2 x 2` special-fibre Hessian
chart.**  The all-minors branch would make the determinant zero, contradicting
the unit clock. -/
theorem ScaleAwareAdaptiveGeometricRestartState.zeroDefect_exactActiveFourBlock
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    Nonempty (AdaptiveAlignedSmithCanonicalExactActiveFourBlock s) := by
  rcases scaleAwareHessian_exactActive_or_rankOne s with hactive | hall
  · exact hactive
  · let H := scaleAwareSpecialHessianFourBlock s
    have hdx : H.d * H.x - H.r * H.r = 0 := by
      have h := hall (1 : Fin 4) 1 2 2
      simpa [H, GeneralFourBlock.matrix] using h
    have hdz : H.d * H.z - H.s * H.s = 0 := by
      have h := hall (1 : Fin 4) 1 3 3
      simpa [H, GeneralFourBlock.matrix] using h
    have hxz : H.x * H.z - H.y * H.y = 0 := by
      have h := hall (2 : Fin 4) 2 3 3
      simpa [H, GeneralFourBlock.matrix] using h
    have hdy : H.d * H.y - H.r * H.s = 0 := by
      have h := hall (1 : Fin 4) 1 2 3
      simpa [H, GeneralFourBlock.matrix, mul_comm] using h
    have hdet0 : H.determinantCore = 0 :=
      H.determinantCore_eq_zero_of_transverse_rankOne hdx hdz hxz hdy
    have hdet1 : H.determinantCore = 1 := by
      simpa [H] using s.zeroDefect_specialHessianDet_one hzero
    rw [hdet1] at hdet0
    exact (one_ne_zero hdet0).elim

/-- Complete zero-defect rank-three geometry, retaining the actual active
four-block beside its Schur/rank-three exhaustion. -/
structure AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  source_zero : s.rawDefect = 0
  chart : AdaptiveAlignedSmithCanonicalExactActiveFourBlock s
  geometry : AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry
    chart complexity

/-- **Every zero-defect scale-aware state already carries complete rank-three
geometry.** -/
noncomputable def
    ScaleAwareAdaptiveGeometricRestartState.zeroDefect_completeRankThreeGeometry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hzero : s.rawDefect = 0) :
    AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry s complexity := by
  let C := Classical.choice (s.zeroDefect_exactActiveFourBlock hzero)
  exact {
    source_zero := hzero
    chart := C
    geometry := C.rankThreeGeometry complexity
  }

end

end HC4.Valuation
