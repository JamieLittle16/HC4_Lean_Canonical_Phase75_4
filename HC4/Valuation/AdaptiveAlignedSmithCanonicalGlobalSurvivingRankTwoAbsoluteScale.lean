import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentationTraceInvariant
import HC4.Valuation.AdaptiveAlignedSmithRankOneStageProgress
import Mathlib.Tactic

/-!
# A18.4.7: surviving rank-two exit at the honest absolute scale

The provenance trace now tells us exactly when an `internalPresentation` came
from the surviving exact-clock branch.  The old surviving-packet machinery is
already geometry-carrying, but its fixed-scale progress theorem is phrased on
legacy adaptive states and therefore views both source and target at scale `1`.

That scale reset is harmless locally but cannot be used in the final global
assembly: the honest aligned outer presentation lives at absolute scale

    alignedSmithRamificationIndex * s.scale.

This file supplies the missing scale lift.  An ordinary adaptive state may be
recorded at any positive *absolute bookkeeping scale* without changing its
polynomial family or any discrete episode coordinate.  Consequently a
certified fixed-scale progress theorem between two ordinary adaptive states
lifts verbatim to certified same-scale progress when both are recorded at the
same positive absolute scale.

Applying this to an actual `AdaptiveAlignedSmithRankTwoPacketEndpoint` turns
the surviving exact-clock rank-two branch into

    source --pure aligned presentation--> outer
           --geometry-carrying rank-two progress--> target

at the real absolute outer scale.  Thus this surviving subbranch is a sound
`AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro`; no scale-1 reset and
no repair-only relabeling occurs.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Record an ordinary adaptive state at an existing absolute scale -/

/-- Keep the exact polynomial parameter of an ordinary adaptive state, while
recording that parameter at a caller-supplied positive absolute scale.

Unlike `parameterRamifiedScaleAwareState`, this performs **no new parameter
ramification** and therefore does not multiply the raw Hessian clock.  It is
intended for geometry already constructed inside an episode whose absolute
scale is known from provenance. -/
def AdaptiveGeometricRestartState.toScaleAwareAt
    (a : AdaptiveGeometricRestartState (K := K))
    (scale : ℕ)
    (hscale : 0 < scale) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) where
  rawDefect := a.defect
  scale := scale
  scale_pos := hscale
  degreeCap := a.degreeCap
  sourceComplexity := a.sourceComplexity
  repair := a.repair
  family := a.family
  movingSection := a.movingSection
  hessianDefect := a.hessianDefect
  nonlinearDegreeBound := a.nonlinearDegreeBound
  exactCollision := a.exactCollision
  sectionSpecial := a.sectionSpecial

@[simp]
theorem AdaptiveGeometricRestartState.toScaleAwareAt_rawDefect
    (a : AdaptiveGeometricRestartState (K := K))
    (scale : ℕ) (hscale : 0 < scale) :
    (a.toScaleAwareAt scale hscale).rawDefect = a.defect := rfl

@[simp]
theorem AdaptiveGeometricRestartState.toScaleAwareAt_scale
    (a : AdaptiveGeometricRestartState (K := K))
    (scale : ℕ) (hscale : 0 < scale) :
    (a.toScaleAwareAt scale hscale).scale = scale := rfl

@[simp]
theorem AdaptiveGeometricRestartState.toScaleAwareAt_repair
    (a : AdaptiveGeometricRestartState (K := K))
    (scale : ℕ) (hscale : 0 < scale) :
    (a.toScaleAwareAt scale hscale).repair = a.repair := rfl

@[simp]
theorem AdaptiveGeometricRestartState.toScaleAwareAt_sourceComplexity
    (a : AdaptiveGeometricRestartState (K := K))
    (scale : ℕ) (hscale : 0 < scale) :
    (a.toScaleAwareAt scale hscale).sourceComplexity = a.sourceComplexity := rfl

@[simp]
theorem AdaptiveGeometricRestartState.toScaleAwareAt_family
    (a : AdaptiveGeometricRestartState (K := K))
    (scale : ℕ) (hscale : 0 < scale) :
    (a.toScaleAwareAt scale hscale).family = a.family := rfl

/-- The ordinary aligned endpoint, recorded at the aligned absolute scale, is
literally the source-honest outer state used by the global presentation
certificate. -/
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_toScaleAwareAt_eq_outer
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap) :
    (E.toAdaptiveState s).toScaleAwareAt
        (alignedSmithRamificationIndex * s.scale)
        (Nat.mul_pos alignedSmithRamificationIndex_pos s.scale_pos) =
      E.toOuterScaleAwareState s := by
  rfl

/-! ## Lift fixed-scale progress without resetting the absolute scale -/

/-- Fixed-scale episode progress depends only on raw defect, repair rank and
source complexity.  Hence a certified scale-1 theorem between ordinary
adaptive states remains the same strict episode theorem when both states are
recorded at one common positive absolute scale. -/
theorem CertifiedFixedScaleEpisodeProgress.toSameScaleAt
    (RR : RepairRanking)
    {source target : AdaptiveGeometricRestartState (K := K)}
    (hprogress : CertifiedFixedScaleEpisodeProgress RR
      target.toScaleAware source.toScaleAware)
    (scale : ℕ)
    (hscale : 0 < scale) :
    CertifiedSameScaleEpisodeProgress RR
      (target.toScaleAwareAt scale hscale)
      (source.toScaleAwareAt scale hscale) := by
  refine ⟨rfl, ?_⟩
  change FixedScaleEpisodeKey.Lt
    (target.defect, (RR.rank target.repair, target.sourceComplexity))
    (source.defect, (RR.rank source.repair, source.sourceComplexity))
  change FixedScaleEpisodeKey.Lt
    (target.defect, (RR.rank target.repair, target.sourceComplexity))
    (source.defect, (RR.rank source.repair, source.sourceComplexity)) at hprogress
  exact hprogress

/-! ## The surviving rank-two packet is now a genuine absolute-scale macro -/

/-- The geometry-carrying rank-two successor of a surviving aligned packet is
strict progress from the honest outer aligned presentation at its actual
absolute scale. -/
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.certifiedSameAbsoluteScaleProgress_from_outer
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    let outer := W.original.aligned.toOuterScaleAwareState s
    let target :=
      R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAwareAt
        outer.scale outer.scale_pos
    CertifiedSameScaleEpisodeProgress RR target outer := by
  dsimp only
  let a := W.original.aligned.toAdaptiveState s
  let q := alignedSmithRamificationIndex * s.scale
  let hq : 0 < q := Nat.mul_pos alignedSmithRamificationIndex_pos s.scale_pos
  have hfixed :
      CertifiedFixedScaleEpisodeProgress RR
        R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAware
        a.toScaleAware := by
    simpa [a] using
      R2.certifiedFixedScaleProgress_from_alignedState RR hsrepair
  have hlift :=
    CertifiedFixedScaleEpisodeProgress.toSameScaleAt
      (K := K) RR hfixed q hq
  have hsource :
      a.toScaleAwareAt q hq =
        W.original.aligned.toOuterScaleAwareState s := by
    dsimp [a, q, hq]
    exact W.original.aligned.toAdaptiveState_toScaleAwareAt_eq_outer s
  rw [hsource] at hlift
  simpa [q, hq] using hlift

/-- **First direct consumption of a surviving presentation origin.**

If the surviving exact-clock packet enters its actual rank-two continuation,
then the old scale-1 local theorem lifts to the aligned outer scale and
composes with the source-honest aligned presentation.  The resulting global
macro retains the real rank-two successor family. -/
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.globalRamifiedStrictMacro_of_survivingExactClock
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (clock_eq :
      W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s := by
  let outer := W.original.aligned.toOuterScaleAwareState s
  let target :=
    R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAwareAt
      outer.scale outer.scale_pos
  have hmove : HasCertifiedRamifiedEpisodeInternalMove outer s := by
    exact ⟨W.original.aligned.certifiedOuterInternal_of_defect_eq s clock_eq⟩
  have hprogress : CertifiedSameScaleEpisodeProgress RR target outer := by
    simpa [outer, target] using
      R2.certifiedSameAbsoluteScaleProgress_from_outer RR hsrepair
  exact .mk outer target hmove hprogress

end

end HC4.Valuation
