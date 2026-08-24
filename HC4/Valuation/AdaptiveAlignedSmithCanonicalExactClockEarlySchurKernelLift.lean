import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockEarlySchurRawRay
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurSpecialKernelLift
import Mathlib.Tactic

/-!
# Polynomial full-kernel lift on the exact-clock early Schur branch

The raw-ray prefix is source-safe but still binary.  The generic cleared
four-block identity now lets us attach to every `earlySchurTangential`
constructor a nonzero *polynomial* full-kernel vector of the honest
special-fibre Hessian block.

No claim of constant source direction is made here.  That is deliberately
the next theorem boundary: the remaining Smith/RS2 argument must prove that
this polynomial kernel vector has constant projective source direction, or
produce certified rank-two repair.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Exact polynomial-kernel datum required from an early Schur constructor. -/
def AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem.HasEarlySchurPolynomialKernel
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) : Prop :=
  ∀ (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
      (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder),
    P.geometry =
        AdaptiveAlignedSmithCanonicalExactClockFinalLocalGeometry.earlySchurTangential
          C hlt htangential →
      Nonempty C.DenominatorClearedSpecialSchurKernelData

namespace AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

/-- Every early Schur final-local constructor already carries the nonzero
polynomial full-kernel lift of its raw special Schur line. -/
theorem hasEarlySchurPolynomialKernel
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) :
    P.HasEarlySchurPolynomialKernel := by
  intro C hlt htangential hgeometry
  exact C.exists_denominatorClearedSpecialSchurKernelData

end AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

end

end HC4.Valuation
