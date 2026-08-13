import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingRelativeFirstLayer
import HC4.Valuation.AdaptiveAlignedSmithExactSchurClock
import Mathlib.Tactic

/-!
# First actual deformation versus the closing Schur clock

Let `C` be an honest chart-aware rank-one Schur closing and let

    j = C.firstActualLayerOrder

be the least positive *actual* parameter order of the same right-recentered
source family.

The retained exact Schur clock closes at

    firstOrder = defect = Delta.

By definition of the first positive transverse Schur order, every order
strictly below `Delta` has zero aligned off-diagonal and zero aligned kernel
coefficient.  Thus any genuine source deformation occurring before closure
is forced to move only along the already-active rank-one Schur direction.

This is the precise, source-linked pre-closing tangency statement needed for
the next absorption/removability argument.

If the first actual source layer occurs exactly at `Delta`, then the closing
clock says that same order is genuinely transverse.  Hence the first actual
deformation has a clean three-way timing picture:

* `j < Delta`: Schur-tangential;
* `j = Delta`: genuinely transverse direct closing;
* `Delta < j`: a remaining causality case, to be ruled out by showing that a
  transverse Hessian coefficient at order `Delta` cannot precede every
  actual source parameter layer.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- An order is Schur-tangential for the retained closing clock when both
transverse aligned Schur coefficients vanish there.  The active Schur entry
is deliberately unrestricted. -/
def IsClosingClockSchurTangentialOrder
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (n : ℕ) : Prop :=
  C.chartData.clock.series.offDiag.coeff n = 0 ∧
    C.chartData.clock.series.kernel.coeff n = 0

/-- Every order strictly below determinant closure is Schur-tangential. -/
theorem schurTangentialOrder_of_lt_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {n : ℕ}
    (hn : n < B.aligned.endpoint.defect) :
    C.IsClosingClockSchurTangentialOrder n := by
  let S := C.chartData.clock
  have hlt : n < S.firstOrder := by
    dsimp [S]
    rw [C.closing.1]
    exact hn
  have hlt' :
      n < S.series.firstPositiveTransverseOrder S.hasTransverse := by
    simpa only [AdaptiveAlignedExactRankOneSchurClock.firstOrder] using hlt
  constructor
  · exact
      S.series.offDiag_coeff_eq_zero_of_lt_first
        S.hasTransverse hlt'
  · exact
      S.series.kernel_coeff_eq_zero_of_lt_first
        S.hasTransverse hlt'

/-- In particular the genuine first actual source deformation is purely
Schur-tangential whenever it occurs before the determinant-closing order. -/
theorem firstActualLayer_schurTangential_of_lt_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpre :
      C.firstActualLayerOrder <
        B.aligned.endpoint.defect) :
    C.IsClosingClockSchurTangentialOrder
      C.firstActualLayerOrder := by
  exact C.schurTangentialOrder_of_lt_defect hpre

/-- Source-linked form: in the pre-closing case the special fibre of the
canonical relative first deformation is the actual coefficient potential at
an order at which both aligned transverse Schur coefficients vanish. -/
theorem relativeFirstActualDeformation_preclosing_tangency
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpre :
      C.firstActualLayerOrder <
        B.aligned.endpoint.defect) :
    polynomialFamilySpecialFiber
        C.relativeFirstActualDeformationFamily =
      familyParameterLayer C.family C.firstActualLayerOrder ∧
    C.IsClosingClockSchurTangentialOrder
      C.firstActualLayerOrder := by
  exact
    ⟨C.relativeFirstActualDeformation_specialFiber,
      C.firstActualLayer_schurTangential_of_lt_defect hpre⟩

/-- At the exact closing order the aligned Schur clock is genuinely
transverse. -/
theorem closingOrder_transverse
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.chartData.clock.series.offDiag.coeff
          B.aligned.endpoint.defect ≠ 0 ∨
      C.chartData.clock.series.kernel.coeff
          B.aligned.endpoint.defect ≠ 0 := by
  exact C.closing.2

/-- Therefore an order equal to the closing defect cannot be
Schur-tangential. -/
theorem not_schurTangentialOrder_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    ¬ C.IsClosingClockSchurTangentialOrder
        B.aligned.endpoint.defect := by
  intro htan
  rcases C.closingOrder_transverse with hoff | hker
  · exact hoff htan.1
  · exact hker htan.2

/-- If the first actual source layer occurs at the closing defect, then that
same actual layer order is genuinely transverse. -/
theorem firstActualLayer_transverse_of_eq_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq :
      C.firstActualLayerOrder =
        B.aligned.endpoint.defect) :
    C.chartData.clock.series.offDiag.coeff
          C.firstActualLayerOrder ≠ 0 ∨
      C.chartData.clock.series.kernel.coeff
          C.firstActualLayerOrder ≠ 0 := by
  rw [heq]
  exact C.closingOrder_transverse

/-- Complete timing trichotomy for the least positive actual source
deformation relative to the exact rank-one closing clock. -/
theorem firstActualLayer_timing_trichotomy
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder <
        B.aligned.endpoint.defect ∧
      C.IsClosingClockSchurTangentialOrder
        C.firstActualLayerOrder) ∨
    (C.firstActualLayerOrder =
        B.aligned.endpoint.defect ∧
      (C.chartData.clock.series.offDiag.coeff
            C.firstActualLayerOrder ≠ 0 ∨
       C.chartData.clock.series.kernel.coeff
            C.firstActualLayerOrder ≠ 0)) ∨
    B.aligned.endpoint.defect <
      C.firstActualLayerOrder := by
  rcases lt_trichotomy
      C.firstActualLayerOrder
      B.aligned.endpoint.defect with
    hpre | heq | hpost
  · exact Or.inl
      ⟨hpre, C.firstActualLayer_schurTangential_of_lt_defect hpre⟩
  · exact Or.inr (Or.inl
      ⟨heq, C.firstActualLayer_transverse_of_eq_defect heq⟩)
  · exact Or.inr (Or.inr hpost)

/-- A compact first-deformation outcome used by the next local theorem. -/
inductive AdaptiveAlignedSmithRankOneFirstActualLayerOutcome
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop
  | preclosingTangential
      (hpre :
        C.firstActualLayerOrder <
          B.aligned.endpoint.defect)
      (hfibre :
        polynomialFamilySpecialFiber
            C.relativeFirstActualDeformationFamily =
          familyParameterLayer C.family C.firstActualLayerOrder)
      (htangent :
        C.IsClosingClockSchurTangentialOrder
          C.firstActualLayerOrder)
  | directClosing
      (heq :
        C.firstActualLayerOrder =
          B.aligned.endpoint.defect)
      (htransverse :
        C.chartData.clock.series.offDiag.coeff
              C.firstActualLayerOrder ≠ 0 ∨
          C.chartData.clock.series.kernel.coeff
              C.firstActualLayerOrder ≠ 0)
  | sourceLayerAfterClosing
      (hpost :
        B.aligned.endpoint.defect <
          C.firstActualLayerOrder)

/-- Package the timing trichotomy together with the honest relative first
deformation fibre. -/
theorem firstActualLayerOutcome
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    AdaptiveAlignedSmithRankOneFirstActualLayerOutcome C := by
  rcases C.firstActualLayer_timing_trichotomy with
    hpre | hclose | hpost
  · exact .preclosingTangential
      hpre.1
      C.relativeFirstActualDeformation_specialFiber
      hpre.2
  · exact .directClosing hclose.1 hclose.2
  · exact .sourceLayerAfterClosing hpost

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
