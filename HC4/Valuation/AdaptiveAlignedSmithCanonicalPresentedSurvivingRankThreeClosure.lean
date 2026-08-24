import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedSurvivingLosslessRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPacketRankThreeClosure
import Mathlib.Tactic

/-!
# A18.4.85: surviving degree-at-least-three exits are already rank three

A18.4.77 retains four honest non-boundary outcomes of a presented surviving
wall.  Two of them are the degree-at-least-three branches:

* a rigid packet after canonical Smith exposure, carrying an exact scalar
  zero-Schur block; and
* a nonrigid packet-family continuation, carrying the actual matrix exposure.

A18.4.80 and A18.4.81 now consume both objects completely to rank-three
geometry.  The remaining exposure-boundary constructor is contradictory by
the same canonical-boundary exclusion already used in the global boundary
closure.

Consequently the only surviving-wall output which is not yet rank three is
the saturated-kernel opening.  This is precisely the branch whose rank-two
provenance is being strengthened separately; it is deliberately retained
rather than hidden behind a repair tag here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Genuine rank-three geometry retained by a presented surviving wall. -/
inductive AdaptiveAlignedSmithCanonicalPresentedSurvivingRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ) : Type (u + 1)
  | rigidExposure
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) D.presented W P)
      (hD : 3 ≤ P.degree)
      (Q : AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
        RR D.presented W P R hD complexity)
      (geometry : AdaptiveAlignedSmithCanonicalCompleteScalarRankThreeGeometry
        Q.geometry.zeroSchur complexity)
  | packetFamily
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) D.presented W)
      (hD : 3 ≤ P.degree)
      (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
        (K := K) D.presented W P complexity)
      (geometry : AdaptiveAlignedSmithCanonicalPacketRankThreeProgress
        D.presented W P complexity R2 hD)

/-- Lossless surviving-wall frontier after consuming every degree-at-least-three
rank-two packet. -/
inductive AdaptiveAlignedSmithCanonicalPresentedSurvivingRankThreeOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | completeKernel
      (P : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
          RR source complexity))
  | rankThree
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedSurvivingRankThreeGeometry
          RR D complexity))

/-- **A18.4.85 surviving-wall rank-three closure.**

After this theorem, the surviving side has no rigid-exposure, packet-family,
or boundary leaf.  The sole unfinished geometric producer is the explicit
saturated-kernel opening. -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.rankThreeClosure
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedSurvivingRankThreeOutcome
      RR D complexity := by
  cases D.losslessRankTwoReduction RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero

  | completeKernel P =>
      exact .completeKernel P

  | rigidExposure W P R hD hQ =>
      rcases hQ with ⟨Q⟩
      let G := exactScalarZeroSchur_completeRankThreeGeometry
        Q.geometry.zeroSchur complexity
      exact .rankThree ⟨.rigidExposure W P R hD Q G⟩

  | packetFamily W P hD R2 =>
      cases R2.rankThreeClosure D.presented W P complexity hD with
      | zeroDefect hzero =>
          have hpresentedZero : D.presented.rawDefect = 0 := by
            have hzero' : W.original.aligned.endpoint.defect = 0 := by
              simpa [
                AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState]
                using hzero
            have hclock :
                W.original.aligned.endpoint.defect = D.presented.rawDefect := by
              simpa [
                AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
                using D.defect_eq
            rw [hclock] at hzero'
            exact hzero'
          exact .zeroDefect
            (D.sourcePresentation.source_rawDefect_eq_zero_of_target
              hpresentedZero)
      | rankThree G =>
          exact .rankThree ⟨.packetFamily W P hD R2 G⟩

  | exposureBoundaryPresentation E target target_eq hmove =>
      exact ((E.exposure.noCanonicalSectionBoundary E.W) E.boundary).elim

end

end HC4.Valuation
