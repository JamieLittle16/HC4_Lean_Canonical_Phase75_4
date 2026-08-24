import HC4.Valuation.AdaptiveAlignedSmithCanonicalExposureNoBoundary
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingWallClosure
import Mathlib.Tactic

/-!
# A18.4.38: presentation-free exact-clock frontier

A18.4.36 absorbs every aligned section-boundary head into a finite canonical
classification.  A18.4.37 proves that the only presentation which could still
survive that absorber -- a canonical Smith-exposure section boundary -- is in
fact impossible.

This file performs only the final lossless splice.  The resulting exact-clock
frontier has no presentation constructor at all.  Importantly, it does **not**
collapse the geometry-carrying rank-two progress structures into the generic
ramified-macro interface: their already-proved `globalProgress` fields remain
available for the final recursion.

The only outputs are therefore

* literal zero raw defect;
* an honest ramified raw-defect spend;
* one of the four geometry-carrying rank-two progress packets; or
* a source-honest ramified strict macro already produced by the canonical
  blocker/surviving closures.

No new progress measure, homogeneity assumption, or repair-only transition is
introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A canonical exposure-boundary endpoint is contradictory.  Keeping this as
an endpoint-level theorem makes every later presentation eliminator a one-line
case rather than redoing the ramification arithmetic of A18.4.37. -/
theorem AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.impossible
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) source) :
    False := by
  exact (E.exposure.noCanonicalSectionBoundary E.W) E.boundary

/-- Final exact-clock outcome after all neutral presentations have been
eliminated.  Every rank-two constructor still retains its actual geometric
witness and its source-honest global progress certificate. -/
inductive AdaptiveAlignedSmithCanonicalPresentationFreeExactClockOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | stationaryRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress
          RR s complexity))

  | earlySchurRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress
          RR s complexity))

  | residualRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress
          RR s complexity))

  | zeroSchurRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoProgress
          RR s complexity))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

/-- **A18.4.38 presentation-free exact-clock theorem.**

Starting from the geometry-preserving A18.4.27 frontier:

* a direct exposure boundary contradicts A18.4.37;
* an aligned section boundary is consumed by A18.4.36, whose sole residual
  exposure boundary again contradicts A18.4.37;
* every genuine exit is forwarded without changing its payload.

Thus no zero-cost presentation can ever be handed to recursive termination. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalPresentationFreeExactClockFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentationFreeExactClockOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalExactClockSurvivingClosedFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero

  | ramifiedSpend target h =>
      exact .ramifiedSpend target h

  | stationaryRankTwoProgress D =>
      exact .stationaryRankTwoProgress D

  | earlySchurRankTwoProgress D =>
      exact .earlySchurRankTwoProgress D

  | residualRankTwoProgress D =>
      exact .residualRankTwoProgress D

  | zeroSchurRankTwoProgress D =>
      exact .zeroSchurRankTwoProgress D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | exposureBoundaryPresentation E target target_eq hmove =>
      exact E.impossible.elim

  | sectionBoundaryInternal B =>
      cases B.soundGlobalAbsorption RR complexity hsrepair with
      | zeroDefect hzero =>
          exact .zeroDefect hzero
      | ramifiedStrictMacro D =>
          exact .ramifiedStrictMacro D
      | exposureBoundaryPresentation presented E target target_eq hmove =>
          exact E.impossible.elim

end

end HC4.Valuation
