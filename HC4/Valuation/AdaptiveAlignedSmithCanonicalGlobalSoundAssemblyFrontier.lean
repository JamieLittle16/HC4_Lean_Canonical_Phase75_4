import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurSourceIntegratedDeparture
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRamifiedSpendClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectReentry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalFinalAssemblySoundness

/-!
# A18.1: sound global assembly frontier

The local A17 stationary/zero-Schur analysis is complete, but the global
recursion must not reintroduce the bookkeeping-only repair bug isolated by
`AdaptiveAlignedSmithCanonicalFinalAssemblySoundness`.

This file starts the genuine global assembly by consuming the two outcomes
which already have honest state-level geometric replacements:

* `rawDefect = 0` is replaced by the explicit transverse Rees re-entry state
  of A17.8, at the same literal scale and with raw defect exactly `6`;
* every bare ramified raw-defect spend is factored through its canonical pure
  ramification presentation and then an honest same-scale strict raw-defect
  exit, using A17.6.

Crucially, the remaining rank-two and projective events are *not* converted
into recursive successors merely from their `RepairProgress` fields.  Their
geometry is retained losslessly.  Likewise a pure ramified presentation is
kept explicitly zero-cost.

Thus this module is an assembly frontier, not a disguised termination theorem.
It is designed so that the next global adapters have exactly the genuinely
geometric obligations left to consume.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Concrete data retained from the zero-defect transverse Rees re-entry.

This is a data-valued structure because the target family and moving section
are actual new geometric data.  No recursive progress is claimed here: the
Rees move raises the raw clock from `0` to `6` and must be consumed as part of
a later global macro. -/
structure AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  source_rawDefect : s.rawDefect = 0
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_rawDefect : target.rawDefect = 6
  sameScale : target.scale = s.scale
  sameDegreeCap : target.degreeCap = s.degreeCap
  sameSourceComplexity : target.sourceComplexity = s.sourceComplexity
  sameRepair : target.repair = s.repair
  target_positive : 0 < target.rawDefect

/-- Package A17.8's explicit zero-defect transverse Rees construction without
changing the repair tag. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exists_globalZeroDefectReentryData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hzero : s.rawDefect = 0) :
    Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s) := by
  rcases s.exists_zeroDefectTransverseReentry hzero with
    ⟨target, hraw, hscale, hdegree, hsource, hrepair, hpositive⟩
  exact ⟨{
    source_rawDefect := hzero
    target := target
    target_rawDefect := hraw
    sameScale := hscale
    sameDegreeCap := hdegree
    sameSourceComplexity := hsource
    sameRepair := hrepair
    target_positive := hpositive
  }⟩

/-- A strict cross-scale macro whose only scale-changing part is a certified
pure ramified re-presentation and whose exit is honest same-scale progress.

This proposition deliberately retains the intermediate `outer` state.  It
must not be collapsed to `CertifiedSameScaleEpisodeProgress RR target source`,
because the source and target need not have the same literal scale. -/
inductive AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop
  | mk
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (internalMove : HasCertifiedRamifiedEpisodeInternalMove outer source)
      (sameScaleProgress : CertifiedSameScaleEpisodeProgress RR target outer)

/-- Every certified ramified spend has the sound two-stage global macro form.
This uses the geometric/raw-defect part of the certificate, not repair
relabeling. -/
theorem AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend.toGlobalStrictMacro
    (RR : RepairRanking)
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hspend :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target source) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source := by
  rcases hspend.exists_internal_then_sameScaleProgress RR with
    ⟨outer, hmove, hprogress⟩
  exact .mk outer target hmove hprogress

/-- **A18.1 sound global assembly outcome.**

Compared with the final A17.17 local frontier:

* zero defect already carries its actual Rees re-entry geometry;
* a bare rational/ramified spend has been replaced by the canonical
  `internal ramification -> same-scale strict exit` macro;
* all zero-Schur/rank-two geometry is retained exactly;
* no generic `withRepairOnly` successor is manufactured.

The `rankTwoMacro` constructor is kept separately from `ramifiedStrictMacro`:
its same-scale progress may contain a finite repair promotion, so final global
recursion is not allowed to consume it until the accompanying rank-two
geometry has been connected to an actual family continuation.
-/
inductive AdaptiveAlignedSmithCanonicalGlobalSoundAssemblyOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefectReentry
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | zeroSchurNondegenerateRankTwo
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSoundRankTwoContinuation
        RR P complexity)
      (hexit : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurNondegenerateRankTwoExit
          RR P complexity D))

  | zeroSchurResidualZeroNondegenerate
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroSchurResidualZeroNondegenerateExit
          P.carrier.chartData.zeroData))

  | zeroSchurSourceIntegratedProjectiveDeparture
      (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
      (D : AdaptiveAlignedSmithCanonicalZeroSchurSourceIntegratedProjectiveDeparture
        P.carrier.chartData.zeroData complexity)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A18.1 first sound global assembly theorem.**

Every canonical rank-one stationary-planar-core state reaches the global
frontier above.  This theorem intentionally does not use
`alignedSmithCanonicalGlobalMacroFrontier_concrete` or the generic A17.9 rank
ladder: those interfaces can create strict numerical progress after changing
only `RepairState` and therefore are unsuitable as final recursive edges.
-/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalSoundAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSoundAssemblyOutcome RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreSourceIntegratedFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefectReentry (s.exists_globalZeroDefectReentryData hzero)
  | ramifiedSpend target hspend =>
      exact .ramifiedStrictMacro (hspend.toGlobalStrictMacro RR)
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | zeroSchurNondegenerateRankTwo P D hexit =>
      exact .zeroSchurNondegenerateRankTwo P D hexit
  | zeroSchurResidualZeroNondegenerate P D =>
      exact .zeroSchurResidualZeroNondegenerate P D
  | zeroSchurSourceIntegratedProjectiveDeparture P D =>
      exact .zeroSchurSourceIntegratedProjectiveDeparture P D
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
