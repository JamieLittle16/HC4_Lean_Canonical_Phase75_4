import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningFilteredRankThreeClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedBlockerRankThreePartialClosure
import Mathlib.Tactic

/-!
# A18.4.99: retained presented kernel packets close soundly at rank three

Several earlier A18 wrappers were named `...RankTwoProgress`.  Their *geometry*
was honest: they retain the actual saturated opening, the first-contact
monomial, and the diagonal/mixed Hessian witness.  What was too strong was the
immediate interpretation of one Hessian entry as a rank-one to rank-two
promotion.

A18.4.90--98 now provide the correct interpretation of exactly that retained
geometry.  Either the opening special fibre already has an honest active
`2 x 2` chart, or its nonzero rank-one Hessian is exhausted by the finite
scalar-Schur ladder.  In both cases complete rank-three geometry is obtained.

This file therefore does not reconstruct any opening and does not use the old
repair-progress field.  It simply forgets the semantic rank-two wrapper and
consumes the concrete first-contact geometry it had already stored.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Any retained complete first-contact geometry has the sound complete
rank-three interpretation, without using a repair tag. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry.completeRankThreeGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalKernelOpeningCompleteRankThreeGeometry
      source complexity := by
  cases G.rankFrontier complexity with
  | rankThree firstContact chart geometry =>
      exact .actual firstContact chart geometry
  | rankOne geometry =>
      exact .filtered geometry geometry.completeFilteredRankThreeGeometry

/-- A historical local rank-two wrapper can be consumed purely through its
retained first-contact geometry. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress.completeRankThreeGeometry
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress
      RR source complexity) :
    AdaptiveAlignedSmithCanonicalKernelOpeningCompleteRankThreeGeometry
      source complexity :=
  P.geometry.completeRankThreeGeometry complexity

/-- Presentation-aware complete rank-three packet.  The presentation is
retained only as provenance; no progress comparison is asserted. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove presented source
  geometry : AdaptiveAlignedSmithCanonicalKernelOpeningCompleteRankThreeGeometry
    presented complexity

/-- Reinterpret an old presented complete-kernel wrapper without using its
`globalProgress` field. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress.completeRankThreeGeometry
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
      RR source complexity) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
      source complexity where
  presented := P.presented
  sourcePresentation := P.sourcePresentation
  geometry := P.local.completeRankThreeGeometry

/-- Blocker rank-three geometry after adding the now-complete saturated-kernel
branch to A18.4.87's already-consumed Schur branches. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerKernelClosedRankThreeGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1)
  | existing
      (geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerRankThreeGeometry
        RR D complexity)
  | kernel
      (geometry : AdaptiveAlignedSmithCanonicalGlobalPresentedKernelOpeningRankThreeGeometry
        source complexity)

/-- Exact blocker frontier after the saturated-kernel seam is closed. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerKernelClosedOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Prop
  | zeroDefect
      (hzero : source.rawDefect = 0)
  | rankThree
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerKernelClosedRankThreeGeometry
          RR D complexity))
  | packetRankTwo
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerPacketRankTwoRemainder
          RR D complexity))
  | stationaryResidual
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker D.presented)
      (P : AdaptiveAlignedSmithCanonicalGlobalPresentedStationaryRankTwoProgress
        RR D S complexity)
      (G : AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
        (K := K) S complexity)

/-- **A18.4.99 kernel-closed blocker frontier.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.kernelClosedRankThreeOutcome
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerKernelClosedOutcome
      RR D complexity := by
  cases D.rankThreePartialClosure RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | completeKernel hP =>
      rcases hP with ⟨P⟩
      exact .rankThree ⟨.kernel P.completeRankThreeGeometry⟩
  | rankThree hG =>
      rcases hG with ⟨G⟩
      exact .rankThree ⟨.existing G⟩
  | packetRankTwo hG =>
      exact .packetRankTwo hG
  | stationaryResidual S P G =>
      exact .stationaryResidual S P G

end

end HC4.Valuation
