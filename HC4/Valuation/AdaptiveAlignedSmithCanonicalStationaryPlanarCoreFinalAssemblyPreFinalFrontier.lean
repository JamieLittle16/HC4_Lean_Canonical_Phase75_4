import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostRigidElimination

/-!
# Final assembly A17.4: local-free pre-final frontier

A17.3F removes the source-complete rigid branch.  Its post-rigid frontier has
one remaining local constructor, the zero-Schur source-ready packet.

At this point no further local geometry is required by the certified episode
interface.  The stationary blocker already retains the exact aligned outer
clock, and the rank-one repair state has the existing certified
rank-one-to-rank-two repair progress.  Therefore the sound outer rank-two
repair macro consumes the zero-Schur constructor directly.

The resulting frontier has no local geometric constructor at all.  Every
state is now either

* zero defect;
* an honest ramified raw-defect spend;
* a certified ramified presentation followed by same-scale rank-two progress;
  or
* an already-certified internal presentation change.

This is intentionally the last local theorem before the global HC4 assembly.
No new source geometry, normal form, or classification datum is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Local-free stationary planar-core frontier immediately before the global
HC4 assembly.  In particular there is deliberately no residual local geometry
constructor. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCorePreFinalAssemblyOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : s.rawDefect = 0)
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.4 local-free pre-final frontier.**

The sole post-rigid local case is zero-Schur.  Its stationary blocker already
sits at the exact aligned outer clock, so the existing certified
rank-one-to-rank-two repair macro consumes it immediately.  Thus the next
assembly theorem has no local source geometry left to classify. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCorePreFinalAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePreFinalAssemblyOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCorePostRigidEliminationFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | «local» P =>
      have hrepair :
          RepairProgress
            (rankOneRepairState complexity)
            (rankTwoRepairState complexity) :=
        rankOne_to_rankTwo_repairProgress complexity
      rcases P.stationary.blocker.aligned.exists_outerRankTwoRepairMacro
          RR s complexity hsrepair P.clock_eq hrepair with
        ⟨outer, target, hmove, hprogress⟩
      exact .rankTwoMacro outer target hmove hprogress

end

end HC4.Valuation
