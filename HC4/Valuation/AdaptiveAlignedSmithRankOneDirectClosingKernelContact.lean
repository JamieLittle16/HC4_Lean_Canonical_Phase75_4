import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingContactRouting
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerKernelClock
import Mathlib.Tactic

/-!
# Exact kernel contact at a rank-one direct closing

The source-support audit distinguishes fresh and overlap first actual source
layers.  Before attempting to lift the Schur alignment back to source
coordinates, one subtlety must be kept explicit: the left-pivot alignment in
`RankOneSchurSeriesAlignment` uses coefficients in
`MvPolynomial (Fin 4) K`.  It is therefore a polynomial-valued congruence,
not in general a constant linear source coordinate change.

The invariant source-independent fact is nevertheless very strong.  For an
honest rank-one closing carrier, the aligned kernel Schur series has exact
positive parameter order equal to the Hessian defect:

* every coefficient below `Delta` vanishes;
* the coefficient at `Delta` is nonzero.

Thus the closing is an honest *fresh kernel observable* at exactly `Delta`.
If the first actual source layer also has order `Delta`, then the first source
layer and this exact kernel contact coincide in parameter order.  If the first
source layer is earlier, it is separated strictly from the kernel contact and
is Schur-tangential.

This is the correct interface for the next step: identify when the exact
kernel observable is integrable to an honest source-level quadratic contact,
or show that failure of such a lift forces repair/restart progress.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Exact-order data for the aligned kernel Schur polynomial at a rank-one
closing.  This deliberately records the observable itself rather than
pretending the polynomial-valued Schur congruence is already a source
coordinate transformation. -/
structure AdaptiveAlignedSmithExactKernelClosingContact
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  order : ℕ
  order_eq_defect : order = B.aligned.endpoint.defect
  order_pos : 0 < order
  coeff_ne_zero :
    C.chartData.clock.series.kernel.coeff order ≠ 0
  lower_zero :
    ∀ n : ℕ, n < order →
      C.chartData.clock.series.kernel.coeff n = 0

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Every aligned kernel coefficient strictly below determinant closure
vanishes. -/
theorem closingKernel_coeff_eq_zero_of_lt_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {n : ℕ}
    (hn : n < B.aligned.endpoint.defect) :
    C.chartData.clock.series.kernel.coeff n = 0 := by
  exact (C.schurTangentialOrder_of_lt_defect hn).2

/-- The aligned kernel Schur series has an exact fresh contact at the closing
order `Delta`: it vanishes at every lower parameter order and is nonzero at
`Delta`. -/
noncomputable def exactKernelClosingContact
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    AdaptiveAlignedSmithExactKernelClosingContact C where
  order := B.aligned.endpoint.defect
  order_eq_defect := rfl
  order_pos := C.defect_pos
  coeff_ne_zero := C.closingOrder_kernel_coeff_ne_zero
  lower_zero := by
    intro n hn
    exact C.closingKernel_coeff_eq_zero_of_lt_defect hn

/-- The closing defect is literally in the parameter support of the aligned
kernel observable. -/
theorem defect_mem_closingKernel_support
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    B.aligned.endpoint.defect ∈
      C.chartData.clock.series.kernel.support := by
  exact Polynomial.mem_support_iff.mpr
    C.closingOrder_kernel_coeff_ne_zero

/-- No smaller parameter order lies in the support of the aligned kernel
observable. -/
theorem closingKernel_not_mem_support_of_lt_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {n : ℕ}
    (hn : n < B.aligned.endpoint.defect) :
    n ∉ C.chartData.clock.series.kernel.support := by
  intro hmem
  have hne : C.chartData.clock.series.kernel.coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hmem
  exact hne (C.closingKernel_coeff_eq_zero_of_lt_defect hn)

/-- In the direct-closing equality case, the least actual source-layer order
coincides exactly with the fresh kernel-contact order. -/
theorem firstActualLayerOrder_eq_kernelContactOrder_of_eq_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.firstActualLayerOrder = C.exactKernelClosingContact.order := by
  simpa [exactKernelClosingContact] using heq

/-- In the strict preclosing case the first actual source deformation occurs
strictly before the exact fresh kernel contact. -/
theorem firstActualLayerOrder_lt_kernelContactOrder_of_lt_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpre : C.firstActualLayerOrder < B.aligned.endpoint.defect) :
    C.firstActualLayerOrder < C.exactKernelClosingContact.order := by
  simpa [exactKernelClosingContact] using hpre

/-- **Exact source/kernel timing frontier.**

The first actual source deformation either occurs strictly before the fresh
kernel contact and is Schur-tangential, or it occurs at exactly the same
parameter order as that contact.  There is no post-closing source branch. -/
theorem firstActualLayer_before_or_at_exactKernelContact
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder < C.exactKernelClosingContact.order ∧
      C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder) ∨
    (C.firstActualLayerOrder = C.exactKernelClosingContact.order ∧
      C.chartData.clock.series.kernel.coeff
        C.firstActualLayerOrder ≠ 0) := by
  rcases C.firstActualLayer_kernelTiming with hpre | hclose
  · left
    exact
      ⟨C.firstActualLayerOrder_lt_kernelContactOrder_of_lt_defect hpre.1,
        C.firstActualLayer_schurTangential_of_lt_defect hpre.1⟩
  · right
    refine
      ⟨C.firstActualLayerOrder_eq_kernelContactOrder_of_eq_defect hclose.1,
        hclose.2⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
