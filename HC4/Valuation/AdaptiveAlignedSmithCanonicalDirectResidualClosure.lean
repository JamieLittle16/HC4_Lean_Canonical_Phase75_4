import HC4.Valuation.AdaptiveAlignedSmithCanonicalResidualRankTwoGeometry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurGeometricRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidElimination
import Mathlib.Tactic

/-!
# A18.4.25: direct source-honest closure of the exact-clock residuals

A18.4.23 produces the exact-clock assembly before any historical repair-only
rank-two wrapper is formed.  A18.4.24 gives one geometry-carrying exit for an
arbitrary honest rank-one closing carrier.  This makes most of the older A9--
A16 residual pipeline unnecessary for the final global proof.

The five exact residual constructors can be closed directly from the data they
already contain:

* both closing-carrier constructors use the universal A18.4.24 split: an
  honest ramified raw-defect spend or retained residual rank-two geometry;
* the zero-Schur constructor uses the existing A17.11 nonzero active-Hessian
  chart witness and therefore gives geometry-carrying rank-two progress;
* either rigid packet is compressed to the existing source-complete rigid
  obstruction, then follows the already-green finite chain

      rigid obstruction
        -> maximal linear-power top layer
        -> explicit transverse top kernel
        -> exact mixed-layer cross
        -> literal full-fibre transverse Hessian kernel
        -> honest ramified raw-defect spend.

Thus the only non-exit exact-clock residuals left by this file are precisely
those which were never local stationary obstructions at all:

* `survivingExactClock`, which belongs to the later canonical exposure
  presentation machinery; and
* `sectionBoundaryInternal`, which belongs to the mixed-degree boundary
  machinery closed in A18.4.16--20.

No global homogeneity, synthetic repair progress, or new geometric assumption
is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Zero-Schur geometry as an actual global rank-two edge -/

/-- The A17.11 same-family zero-Schur continuation, promoted to the final
macro key only while retaining its honest nonzero active Hessian minor. -/
structure AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  problem : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s
  continuation :
    AdaptiveAlignedSmithCanonicalZeroSchurGeometryCarryingRankTwoContinuation
      RR problem complexity
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress continuation.target s

/-- Build the global zero-Schur edge directly from an exact residual.  The
repair decrease is accepted only together with A17.11's literal chart-level
rank-two witness. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoProgress.ofResidual
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
    (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker) :
    AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoProgress
      RR s complexity := by
  let P : AdaptiveAlignedSmithCanonicalPostRigidEliminationTerminalLocalProblem s := {
    stationary := S
    clock_eq := clock_eq
    clock_pos := clock_pos
    source := S.toTerminalSourcePacket
    carrier := C
    zeroSchur := S.zeroSchurScaleSoundSourceData C
  }
  let D : AdaptiveAlignedSmithCanonicalZeroSchurGeometryCarryingRankTwoContinuation
      RR P complexity :=
    Classical.choice (P.exists_geometryCarryingRankTwoContinuation
      RR complexity hsrepair)
  have hglobal :
      AdaptiveAlignedSmithCanonicalGlobalMacroProgress D.target s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [D.target_eq]
    simpa [ScaleAwareAdaptiveGeometricRestartState.withRepairOnly, hsrepair] using
      repairState_measure_lt_of_progress D.repairProgress
  exact {
    problem := P
    continuation := D
    globalProgress := hglobal
  }

/-! ## Direct rigid spend -/

/-- A source-complete rigid obstruction is already an honest strict defect
spend; this theorem merely composes the four existing A17.3B--F data maps. -/
theorem AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction.exists_directRamifiedSpend
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rcases R.toRigidTopLayerData with ⟨top⟩
  rcases top.toRigidTopKernelData with ⟨kernel⟩
  rcases kernel.toRigidMixedLayerCrossData with ⟨mixed⟩
  exact mixed.exists_ramifiedSpend S clock_eq

/-- The planar rigid exact-clock residual therefore spends immediately. -/
theorem planarRigid_exactResidual_exists_ramifiedSpend
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
      (K := K) S.blocker)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 P.degree P.packet) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
    source := S.toTerminalSourcePacket
    hall := hall
    packet := .planar P hrigid
  }
  exact R.exists_directRamifiedSpend clock_eq

/-- The `w^2` rigid exact-clock residual spends by the identical source-complete
rigid argument. -/
theorem wSquareRigid_exactResidual_exists_ramifiedSpend
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint
      (K := K) S.blocker)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 3 2 P.degree P.packet) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  let R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S := {
    source := S.toTerminalSourcePacket
    hall := hall
    packet := .wSquare P hrigid
  }
  exact R.exists_directRamifiedSpend clock_eq

/-! ## Close every local residual directly -/

/-- A18.4.25 residual outcome.  There is no stationary local geometry left.
The two presentation-facing constructors are intentionally retained rather
than declared recursive progress. -/
inductive AdaptiveAlignedSmithCanonicalDirectResidualClosureOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | residualRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress
          RR s complexity))

  | zeroSchurRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoProgress
          RR s complexity))

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- Every residual of the geometry-preserving exact-clock assembly closes
without the historical repair-only rank-two macro. -/
theorem AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual.directClosure
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (R : AdaptiveAlignedSmithCanonicalExactClockAssemblyResidual s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalDirectResidualClosureOutcome
      RR s complexity := by
  cases R with
  | earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential packet =>
      rcases S.toTerminalSourcePacket.closingCarrier_ramifiedSpend_or_rankTwoGeometry
          clock_eq complexity C with hspend | hgeometry
      · rcases hspend with ⟨target, h⟩
        exact .ramifiedSpend target h
      · rcases hgeometry with ⟨G⟩
        exact .residualRankTwoProgress
          ⟨AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress.ofGeometry
            RR S complexity hsrepair clock_eq G⟩

  | canonicalEarlierWall S clock_eq clock_pos C heq wall =>
      rcases S.toTerminalSourcePacket.closingCarrier_ramifiedSpend_or_rankTwoGeometry
          clock_eq complexity C with hspend | hgeometry
      · rcases hspend with ⟨target, h⟩
        exact .ramifiedSpend target h
      · rcases hgeometry with ⟨G⟩
        exact .residualRankTwoProgress
          ⟨AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress.ofGeometry
            RR S complexity hsrepair clock_eq G⟩

  | zeroSchur S clock_eq clock_pos C =>
      exact .zeroSchurRankTwoProgress
        ⟨AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoProgress.ofResidual
          RR complexity hsrepair S clock_eq clock_pos C⟩

  | planarRigid S clock_eq clock_pos hall P hrigid =>
      rcases planarRigid_exactResidual_exists_ramifiedSpend
          S clock_eq hall P hrigid with ⟨target, h⟩
      exact .ramifiedSpend target h

  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      rcases wSquareRigid_exactResidual_exists_ramifiedSpend
          S clock_eq hall P hrigid with ⟨target, h⟩
      exact .ramifiedSpend target h

  | survivingExactClock W clock_eq =>
      exact .survivingExactClock W clock_eq

  | sectionBoundaryInternal B =>
      exact .sectionBoundaryInternal B

/-! ## Full exact-clock frontier after direct local closure -/

/-- Exact-clock outcome after every stationary local obstruction has been
removed.  Every rank-two constructor is geometry-carrying. -/
inductive AdaptiveAlignedSmithCanonicalExactClockDirectClosedOutcome
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

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- **A18.4.25 direct closed exact-clock frontier.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockDirectClosedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockDirectClosedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalExactClockGeometryAssemblyFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target h =>
      exact .ramifiedSpend target h
  | stationaryRankTwoProgress D =>
      exact .stationaryRankTwoProgress D
  | earlySchurRankTwoProgress D =>
      exact .earlySchurRankTwoProgress D
  | residual R =>
      cases R.directClosure RR complexity hsrepair with
      | ramifiedSpend target h => exact .ramifiedSpend target h
      | residualRankTwoProgress D => exact .residualRankTwoProgress D
      | zeroSchurRankTwoProgress D => exact .zeroSchurRankTwoProgress D
      | survivingExactClock W clock_eq => exact .survivingExactClock W clock_eq
      | sectionBoundaryInternal B => exact .sectionBoundaryInternal B

end

end HC4.Valuation
