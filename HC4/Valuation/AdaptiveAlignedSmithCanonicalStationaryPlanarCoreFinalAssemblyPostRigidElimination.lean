import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidElimination

/-!
# Final assembly A17.3F: rigid-free local frontier

A17.3F globalises the canonical transverse top-layer kernel to a literal
constant kernel of the complete honest right-recentered special fibre.  The
blocker-native A17.3E exit then gives a certified ramified raw-defect spend.

Consequently the source-complete rigid branch is no longer a local terminal
geometry.  The only surviving local geometry is the zero-Schur source-ready
branch.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- After rigid elimination, zero-Schur is the sole surviving local geometry. -/
structure AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  carrier : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier stationary.blocker
  zeroSchur :
    AdaptiveAlignedSmithZeroSchurScaleSoundSourceData stationary.blocker carrier

/-- The rigid-free local frontier. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostRigidEliminationOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop
  | zeroDefect (hzero : s.rawDefect = 0)
  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend target s)
  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)
  | local (P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.3F rigid elimination frontier.**  Every rigid mixed-layer-cross
terminal is converted to an honest right-recentered constant kernel and spent.
Thus only zero-Schur survives locally. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCorePostRigidEliminationFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostRigidEliminationOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCorePostRigidMixedLayerCrossFrontier
      RR complexity hsrepair with
  | zeroDefect hzero => exact .zeroDefect hzero
  | ramifiedSpend target hspend => exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | «local» P =>
      cases P.geometry with
      | zeroSchurSourceReady C source =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            carrier := C
            zeroSchur := source
          }
      | rigidMixedLayerCross T =>
          rcases T.exists_ramifiedSpend P.stationary P.clock_eq with
            ⟨target, hspend⟩
          exact .ramifiedSpend target hspend

end

end HC4.Valuation
