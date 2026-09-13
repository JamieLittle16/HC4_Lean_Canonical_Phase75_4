import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidMixedLayerCross

/-!
# Final assembly A17.3D: post-rigid-mixed-layer-cross frontier

The rigid branch now carries the exact next occupied ordinary-homogeneous
layer of the literal special fibre, together with every mixed top/next-layer
Hessian-minor equation and the resulting pairwise tangent identities.

The next elimination theorem therefore has no remaining provenance or degree
bookkeeping to perform: it only has to classify/iterate these tangent layers
until the top constant kernel locks through the whole special fibre.
-/

-- The generic two-zero derivative commutation rules are useful for the late
-- finite Hessian rank split, but enabling them here changes the normal form of
-- the already-stable A17 rigid-elimination proofs.  Keep A17 on its original
-- simp basis; the rules are re-enabled at the exact-active A18 boundary.
attribute [-simp] HC4.Newton.pderiv_standardTwoZeroA
attribute [-simp] HC4.Newton.pderiv_standardTwoZeroC

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

inductive AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossTerminalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop
  | zeroSchurSourceReady
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)
  | rigidMixedLayerCross
      (T : AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData S)

structure AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossTerminalGeometry stationary

inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostRigidMixedLayerCrossOutcome
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
  | local (P : AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossTerminalLocalProblem s)
  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A17.3D exact mixed-layer refinement.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCorePostRigidMixedLayerCrossFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePostRigidMixedLayerCrossOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCorePostRigidTopKernelFrontier
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
            geometry := .zeroSchurSourceReady C source
          }
      | rigidTopKernel T =>
          rcases T.toRigidMixedLayerCrossData with ⟨M⟩
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .rigidMixedLayerCross M
          }

end

end HC4.Valuation
