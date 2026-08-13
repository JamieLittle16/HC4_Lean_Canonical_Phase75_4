import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import Mathlib.Tactic

/-!
# Kernel causality at the first actual rank-one closing layer

Let `j` be the first positive actual source layer and `Delta` the exact
rank-one closing defect.  The already-green causality theorem gives

    j <= Delta.

This file sharpens the two possible timings at the level of the retained
exact Schur clock.

* if `j < Delta`, the first source deformation is Schur-tangential, hence its
  aligned kernel coefficient is zero;
* if `j = Delta`, determinant closure forces the aligned kernel coefficient
  to be nonzero.

The second assertion is stronger than the older closing statement, which
only retained `offDiag != 0 or kernel != 0`.  It follows from first-layer
Schur linearisation: at the first transverse order the determinant
coefficient is `leading * kernel`, while exact determinant closure makes
that determinant coefficient nonzero.

Thus deciding whether `j < Delta` is now reduced to a source/collision
question: can the first actual source deformation carry nonzero aligned
kernel curvature?  No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedExactRankOneSchurClock

/-- At the exact defect order the cleared determinant clock has a nonzero
coefficient. -/
theorem determinant_coeff_defect_ne_zero
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E) :
    S.series.determinant.coeff E.defect ≠ 0 := by
  rw [S.schurFactor]
  rw [Polynomial.coeff_mul_X_pow']
  simpa using S.clearedFactor_coeff_zero_ne_zero

/-- **Closing is necessarily a kernel crossing.**

If the first positive transverse Schur order is exactly the determinant
closing order, then the kernel-direction coefficient at that order is
nonzero.  The off-diagonal coefficient may also be nonzero, but it cannot be
the sole cause of determinant closure. -/
theorem kernel_coeff_firstOrder_ne_zero_of_closing
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hclose : S.firstOrder = E.defect) :
    S.series.kernel.coeff S.firstOrder ≠ 0 := by
  have hdet :
      S.series.determinant.coeff S.firstOrder ≠ 0 := by
    simpa [hclose] using S.determinant_coeff_defect_ne_zero
  have hlin :
      S.series.determinant.coeff S.firstOrder =
        S.series.leading * S.series.kernel.coeff S.firstOrder := by
    simpa [FirstRankOneSchurDeparture.determinant,
      RankOneSchurSeries.determinant, firstDeparture] using
      S.firstDeparture.coeff_order_determinant
  intro hkernel
  apply hdet
  rw [hlin, hkernel]
  simp

/-- Defect-indexed form of the same closing-kernel statement. -/
theorem kernel_coeff_defect_ne_zero_of_closing
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hclose : S.firstOrder = E.defect) :
    S.series.kernel.coeff E.defect ≠ 0 := by
  have h := S.kernel_coeff_firstOrder_ne_zero_of_closing hclose
  rw [hclose] at h
  exact h

end AdaptiveAlignedExactRankOneSchurClock

/-! ## Source-linked first actual layer timing -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- In a genuine preclosing source layer the aligned kernel coefficient is
zero. -/
theorem firstActualLayer_kernel_coeff_eq_zero_of_lt_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpre :
      C.firstActualLayerOrder < B.aligned.endpoint.defect) :
    C.chartData.clock.series.kernel.coeff C.firstActualLayerOrder = 0 := by
  exact (C.firstActualLayer_schurTangential_of_lt_defect hpre).2

/-- If the first actual source layer occurs exactly at determinant closure,
then that same actual source layer carries nonzero aligned kernel curvature.
-/
theorem firstActualLayer_kernel_coeff_ne_zero_of_eq_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq :
      C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.chartData.clock.series.kernel.coeff C.firstActualLayerOrder ≠ 0 := by
  have hkernel :=
    C.chartData.clock.kernel_coeff_defect_ne_zero_of_closing C.closing.1
  rw [heq]
  exact hkernel

/-- **Exact kernel-timing dichotomy for the first actual source layer.**

After source/Hessian causality there are only two possibilities:

* `j < Delta`, and the first actual layer has zero aligned kernel
  coefficient;
* `j = Delta`, and the first actual layer has nonzero aligned kernel
  coefficient.

This is the clean interface for the next collision-sensitive test of strict
inequality. -/
theorem firstActualLayer_kernelTiming
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder < B.aligned.endpoint.defect ∧
      C.chartData.clock.series.kernel.coeff C.firstActualLayerOrder = 0) ∨
    (C.firstActualLayerOrder = B.aligned.endpoint.defect ∧
      C.chartData.clock.series.kernel.coeff C.firstActualLayerOrder ≠ 0) := by
  rcases C.firstActualLayer_preclosingTangential_or_directClosing with
    hpre | hclose
  · exact Or.inl ⟨hpre.1, hpre.2.2⟩
  · exact Or.inr
      ⟨hclose.1,
        C.firstActualLayer_kernel_coeff_ne_zero_of_eq_defect hclose.1⟩

/-- At direct closing the old disjunction can be sharpened to the kernel
branch alone. -/
theorem closingOrder_kernel_coeff_ne_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.chartData.clock.series.kernel.coeff B.aligned.endpoint.defect ≠ 0 := by
  exact
    C.chartData.clock.kernel_coeff_defect_ne_zero_of_closing C.closing.1

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
