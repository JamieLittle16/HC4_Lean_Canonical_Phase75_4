import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockEarlySchurKernelLift
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurConstantProjectiveKernel
import Mathlib.Tactic

/-!
# Projective-kernel target on the exact-clock early Schur branch

This file fixes the precise output type for the remaining RS2/Smith theorem.
Stage 3 gives a nonzero polynomial full Hessian-kernel vector.  The hard local
step now has only two meaningful outcomes:

* expose certified repair from nonconstant projective kernel motion; or
* prove that the Stage-3 polynomial kernel has a constant projective source
  direction.

The second alternative is consumed here immediately and converted to an
honest constant source-kernel vector.  Thus later patches never need to
repeat denominator cancellation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Exact projectivisation-to-source-kernel bridge required on an early Schur
final-local constructor. -/
def AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem.HasEarlySchurProjectiveKernelBridge
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) : Prop :=
  ∀ (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
      (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder),
    P.geometry =
        AdaptiveAlignedSmithCanonicalExactClockFinalLocalGeometry.earlySchurTangential
          C hlt htangential →
    ∀ (D : C.DenominatorClearedSpecialSchurKernelData),
      D.HasConstantProjectiveDirection →
      Nonempty C.ConstantSpecialSourceKernelData

namespace AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

/-- Constant projective direction of the Stage-3 polynomial kernel already
upgrades, without any further geometric input, to a genuine constant source
kernel of the honest special-fibre Hessian block. -/
theorem hasEarlySchurProjectiveKernelBridge
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) :
    P.HasEarlySchurProjectiveKernelBridge := by
  intro C hlt htangential hgeometry D hprojective
  exact ⟨hprojective.toConstantSpecialSourceKernelData⟩

end AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

end

end HC4.Valuation
