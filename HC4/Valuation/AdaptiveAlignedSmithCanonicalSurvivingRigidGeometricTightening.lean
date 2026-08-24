import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
import Mathlib.Tactic

/-!
# A18.4.26: tighten surviving-rigid closing exposure provenance

The geometry-preserving surviving-rigid reduction already retains the actual
exposure in every branch.  Its closing constructor was intentionally broad:
it stored a canonical exposure used to construct a nonempty closing endpoint,
but did not expose an equality between that stored exposure and the endpoint's
own exposure field.

For global composition we want a syntactic source of truth.  This tiny adapter
simply re-runs the already-proved `canonicalSpecial_or_boundary` dichotomy on
the closing endpoint's *own* exposure.  Consequently the closing constructor
below carries an actual endpoint together with a canonical-special equation
about exactly `C.exposure`; otherwise the same exposure is returned as a
genuine boundary.

No mathematics, clock comparison, or progress assertion is added here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Tight source-honest form of the surviving rigid local outcome. -/
inductive AdaptiveAlignedSmithCanonicalSurvivingRigidTightOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree) : Prop

  | zeroDefect
      (hzero : (W.original.aligned.toAdaptiveState s).defect = 0)

  | exposureBoundary
      (d : AdaptiveSurvivingWallExposureData
        (W.original.aligned.toAdaptiveState s) W.wall)
      (boundary : Nonempty (AdaptiveSmithExposureSectionBoundary d))

  | rankTwoGeometry
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
          s W P R hD))

  | canonicalClosing
      (C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
        (K := K) s W P R)
      (canonicalSpecial :
        polynomialSectionSpecialPoint C.exposure.rightSection =
          coordinateAxisPoint (K := K) (0 : Fin 4))

/-- Re-run the special-point dichotomy on the closing endpoint's own exposure.
This is the exact provenance shape needed by the global surviving-wall
closure. -/
theorem AdaptiveAlignedSmithRigidPacketEndpoint.geometricTightOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree) :
    AdaptiveAlignedSmithCanonicalSurvivingRigidTightOutcome
      s W P R hD := by
  cases R.geometricOutcome s W P hD with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | exposureBoundary d hboundary =>
      exact .exposureBoundary d hboundary
  | rankTwoGeometry G =>
      exact .rankTwoGeometry G
  | canonicalClosing d hspecial C =>
      rcases C with ⟨C⟩
      rcases C.exposure.canonicalSpecial_or_boundary with
        hcanonical | hboundary
      · exact .canonicalClosing C hcanonical
      · exact .exposureBoundary C.exposure hboundary

end

end HC4.Valuation
