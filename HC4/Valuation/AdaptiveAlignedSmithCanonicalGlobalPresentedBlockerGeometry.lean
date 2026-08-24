import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedEndpointScaleBridge
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockRankTwoGeometry
import HC4.Valuation.AdaptiveAlignedSmithBlockerEndgameProvenance
import Mathlib.Tactic

/-!
# A18.4.32: retain blocker rank-two geometry at the current presented scale

A18.4.30 shows that a boundary-produced canonical blocker is already the
literal currently represented family.  The historical exact-clock wrapper is
therefore the wrong interface for this endpoint: applying it again would add a
second aligned-Smith factor before inspecting geometry which is already
present.

This file reruns only the local right-recentered Hessian split, with no global
clock convention.  Every rank-two alternative retains the concrete witness
which justifies promotion:

* a preterminal rank-one Schur chart;
* a preterminal residual clock on an exact zero-Schur chart;
* a planar quadratic packet escalation; or
* a `w^2` packet escalation.

Only after such a witness exists do we attach the rank-one -> rank-two repair
change to the literal `presented` state.  Closing, transverse-free and rigid
alternatives remain losslessly typed for the next closure patch.

No new ramification, global homogeneity, or bare repair-only recursive edge is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Geometry which actually licenses rank promotion -/

/-- Rank-two geometry living directly on one presented canonical blocker. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerRankTwoGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    Type (u + 1)

  | schurPreterminal
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (preterminal :
        chart.clock.firstOrder < D.blocker.aligned.endpoint.defect)

  | zeroSchurPreterminal
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (residual : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (residual_pos : 0 < chart.zeroData.toClock.residualDefect)
      (residual_clock : residual.defect = chart.zeroData.toClock.residualDefect)
      (preterminal : residual.firstOrder < residual.defect)

  | planarPacket
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) D.blocker)
      (escalation : HasRankTwoPacketEscalation
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquarePacket
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) D.blocker)
      (escalation : HasRankTwoPacketEscalation
        (0 : Fin 4) 3 2 P.degree P.packet)

namespace AdaptiveAlignedSmithCanonicalPresentedBlockerRankTwoGeometry

/-- Every retained Schur rank-two branch contains a literal nonzero mixed
coefficient at its first active order. -/
theorem offDiag_ne_zero_of_schur
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source}
    (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
    (hpre : chart.clock.firstOrder < D.blocker.aligned.endpoint.defect) :
    chart.clock.series.offDiag.coeff chart.clock.firstOrder ≠ 0 :=
  chart.clock.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre

/-- The zero-Schur residual branch carries the analogous concrete witness. -/
theorem offDiag_ne_zero_of_zeroSchur
    (R : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
    (hpre : R.firstOrder < R.defect) :
    R.series.offDiag.coeff R.firstOrder ≠ 0 :=
  R.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre

end AdaptiveAlignedSmithCanonicalPresentedBlockerRankTwoGeometry

/-! ## Lossless local blocker split without an outer-clock convention -/

/-- Local geometric outcome of a presented blocker.  Unlike the old compact
blocker endgame, no constructor contains a bare `RepairProgress`. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBlockerGeometricOutcome
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) : Prop

  | zeroDefect
      (hzero : D.blocker.aligned.endpoint.defect = 0)

  | rankTwoGeometry
      (G : Nonempty
        (AdaptiveAlignedSmithCanonicalPresentedBlockerRankTwoGeometry D))

  | schurClosing
      (chart : AdaptiveAlignedRightRecenteredRankOneSchurChartData D.blocker)
      (closing : chart.clock.firstOrder = D.blocker.aligned.endpoint.defect)
      (transverse :
        chart.clock.series.offDiag.coeff D.blocker.aligned.endpoint.defect ≠ 0 ∨
        chart.clock.series.kernel.coeff D.blocker.aligned.endpoint.defect ≠ 0)

  | zeroSchurClosing
      (chart : AdaptiveAlignedRightRecenteredZeroSchurChartData D.blocker)
      (closing : HasAdaptiveAlignedZeroSchurClosing chart.zeroData)

  | transverseFree
      (allMinors :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho D.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (free :
        ∀ d ∈ D.blocker.aligned.endpoint.rawSpecialFiber.support,
          d (1 : Fin 4) = 0 ∧
          d (2 : Fin 4) = 0 ∧
          d (3 : Fin 4) = 0)

  | planarRigid
      (allMinors :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho D.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) D.blocker)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigid
      (allMinors :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho D.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) D.blocker)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- **A18.4.32 local geometry extraction.**

This is the geometry-preserving A18.4.21 split with its exact-clock wrapper
removed.  It inspects the blocker already carried by `D`, so no additional
aligned transformation occurs. -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.geometricOutcome
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    AdaptiveAlignedSmithCanonicalPresentedBlockerGeometricOutcome D := by
  by_cases hz : D.blocker.aligned.endpoint.defect = 0
  · exact .zeroDefect hz
  have hpos : 0 < D.blocker.aligned.endpoint.defect := Nat.pos_of_ne_zero hz

  rcases D.blocker.exists_exactRightRecenteredHessianChart_or_allMinors with
    hchart | hall

  · let H := Classical.choice hchart
    rcases D.blocker.schur_or_zeroSchur_of_exactChart H hpos with
      hschur | hzero

    · let C := Classical.choice hschur
      rcases C.clock.firstOrder_preterminal_or_closing with hpre | hclose
      · exact .rankTwoGeometry ⟨.schurPreterminal C hpre⟩
      · exact .schurClosing C hclose
          (C.clock.closing_transverse_nonzero hclose)

    · let Z := Classical.choice hzero
      let E := Z.zeroData.toClock
      by_cases hres0 : E.residualDefect = 0
      · exact .zeroSchurClosing Z
          (Or.inl ⟨hres0,
            E.tail_constant_det_ne_zero_of_residual_zero hres0⟩)
      · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
        rcases E.tail_pivot_of_residual_pos hres with hleft | hright
        · let R := E.toRankOneClockLeft hres hleft
          rcases lt_or_eq_of_le R.firstOrder_le_defect with hpre | hclose
          · exact .rankTwoGeometry
              ⟨.zeroSchurPreterminal Z R hres rfl hpre⟩
          · have htrans := R.series.transverse_nonzero_at_first R.hasTransverse
            have hfirst :
                R.series.firstPositiveTransverseOrder R.hasTransverse =
                  R.defect := by
              simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
            rw [hfirst] at htrans
            exact .zeroSchurClosing Z
              (Or.inr ⟨R, hres, rfl, hclose, htrans⟩)
        · let R := E.toRankOneClockRight hres hright
          rcases lt_or_eq_of_le R.firstOrder_le_defect with hpre | hclose
          · exact .rankTwoGeometry
              ⟨.zeroSchurPreterminal Z R hres rfl hpre⟩
          · have htrans := R.series.transverse_nonzero_at_first R.hasTransverse
            have hfirst :
                R.series.firstPositiveTransverseOrder R.hasTransverse =
                  R.defect := by
              simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
            rw [hfirst] at htrans
            exact .zeroSchurClosing Z
              (Or.inr ⟨R, hres, rfl, hclose, htrans⟩)

  · have hall' := hall
    rcases D.blocker.pureLongitudinal_or_quadraticPacket_of_allMinors hall with
      hpure | hplanar | hw

    · rcases D.blocker.pureLongitudinal_transverseFree_or_quadraticPacket
          hpure hall' with hfree | hplanar' | hw'
      · exact .transverseFree hall' hfree
      · rcases hplanar' with ⟨P⟩
        cases P.localOutcome 0 with
        | rigid hrigid => exact .planarRigid hall' P hrigid
        | rankTwo hesc _hprogress =>
            exact .rankTwoGeometry ⟨.planarPacket P hesc⟩
      · rcases hw' with ⟨P⟩
        cases P.localOutcome 0 with
        | rigid hrigid => exact .wSquareRigid hall' P hrigid
        | rankTwo hesc _hprogress =>
            exact .rankTwoGeometry ⟨.wSquarePacket P hesc⟩

    · rcases hplanar with ⟨P⟩
      cases P.localOutcome 0 with
      | rigid hrigid => exact .planarRigid hall' P hrigid
      | rankTwo hesc _hprogress =>
          exact .rankTwoGeometry ⟨.planarPacket P hesc⟩

    · rcases hw with ⟨P⟩
      cases P.localOutcome 0 with
      | rigid hrigid => exact .wSquareRigid hall' P hrigid
      | rankTwo hesc _hprogress =>
          exact .rankTwoGeometry ⟨.wSquarePacket P hesc⟩

/-! ## Geometry-carrying rank promotion at the current absolute scale -/

/-- Rank promotion on a presented blocker, retaining the exact geometry which
licensed it.  The target is literally `D.presented` with only the finite repair
coordinate changed. -/
structure AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ) : Type (u + 1) where
  geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerRankTwoGeometry D
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = D.presented.withRepairOnly (rankTwoRepairState complexity)
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target D.presented
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- Attach the finite repair change only after a retained blocker witness is
available. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (G : AdaptiveAlignedSmithCanonicalPresentedBlockerRankTwoGeometry D) :
    AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
      RR D complexity := by
  let target := D.presented.withRepairOnly (rankTwoRepairState complexity)

  have hpresentedRepair :
      D.presented.repair = rankOneRepairState complexity := by
    rcases D.sourcePresentation with ⟨hmove⟩
    rw [hmove.repair_eq]
    exact hsrepair

  have hrepair :
      RepairProgress D.presented.repair (rankTwoRepairState complexity) := by
    simpa [hpresentedRepair] using
      rankOne_to_rankTwo_repairProgress complexity

  have hprogress : CertifiedSameScaleEpisodeProgress RR target D.presented := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair

  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [show target.repair = rankTwoRepairState complexity by rfl, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)

  exact {
    geometry := G
    target := target
    target_eq := rfl
    presentedProgress := hprogress
    globalProgress := hglobal
  }

/-- A geometry-carrying presented-blocker rank promotion is an honest global
strict macro from the original source. -/
theorem AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress.toRamifiedStrictMacro
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
      RR D complexity) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source :=
  .mk D.presented P.target D.sourcePresentation P.presentedProgress

/-- Regression: rank promotion does not replace the current polynomial family. -/
@[simp]
theorem AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress.target_family
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source}
    {complexity : ℕ}
    (P : AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRankTwoProgress
      RR D complexity) :
    P.target.family = D.presented.family := by
  rw [P.target_eq]
  rfl

end

end HC4.Valuation
