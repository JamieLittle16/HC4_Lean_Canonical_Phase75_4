import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPointedRankTwoProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockStationaryEndgame
import Mathlib.Tactic

/-!
# A18.4.21: retain the geometry of every stationary rank-two promotion

The exact-clock stationary endgame is mathematically sound, but its historical
`rankTwoMacro` interface remembers only

* the exact outer ramified presentation, and
* a same-scale `RepairProgress` step.

That interface is too weak for final recursion because it forgets *why* the
rank-one -> rank-two promotion was justified.

The geometry is already present immediately before the old wrapper:

* a rank-one Schur chart has a genuinely preterminal nonzero off-diagonal
  first layer;
* a zero-Schur chart has a residual rank-one clock with the same genuinely
  preterminal off-diagonal first layer;
* a planar quadratic packet carries `HasRankTwoPacketEscalation`;
* the `w^2` packet carries `HasRankTwoPacketEscalation`.

This file preserves those witnesses.  It reruns only the already-green local
case split, without changing any mathematical branch.  Once a witness is
retained, the finite repair promotion is attached to the honest aligned outer
family exactly as in A18.4.1: the source first moves by the certified 20-fold
presentation, then the repair rank changes on that *same actual family*.

No homogeneity hypothesis, repair-only source relabel, or new geometric lemma
is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Geometry which actually justifies a stationary rank-two promotion -/

/-- Source-honest rank-two geometry at one stationary exact-clock blocker.

Each constructor retains an object tied directly to the blocker family.  The
preterminal Schur constructors store the strict timing inequality itself,
rather than merely the generic rank-one -> rank-two repair relation. -/
inductive AdaptiveAlignedSmithCanonicalStationaryRankTwoGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    Type (u + 1)

  | schurPreterminal
      (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData S.blocker)
      (preterminal : D.clock.firstOrder < S.blocker.aligned.endpoint.defect)

  | zeroSchurPreterminal
      (Z : AdaptiveAlignedRightRecenteredZeroSchurChartData S.blocker)
      (R : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (residual_pos : 0 < Z.zeroData.toClock.residualDefect)
      (residual_clock : R.defect = Z.zeroData.toClock.residualDefect)
      (preterminal : R.firstOrder < R.defect)

  | planarPacket
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (escalation : HasRankTwoPacketEscalation
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquarePacket
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (escalation : HasRankTwoPacketEscalation
        (0 : Fin 4) 3 2 P.degree P.packet)

namespace AdaptiveAlignedSmithCanonicalStationaryRankTwoGeometry

/-- A preterminal ordinary Schur witness contains a literal nonzero mixed
Schur coefficient on the retained honest chart. -/
theorem schur_offDiag_ne_zero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData S.blocker)
    (hpre : D.clock.firstOrder < S.blocker.aligned.endpoint.defect) :
    D.clock.series.offDiag.coeff D.clock.firstOrder ≠ 0 :=
  D.clock.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre

/-- The residual zero-Schur rank-one witness likewise contains a literal
nonzero mixed coefficient. -/
theorem zeroSchur_offDiag_ne_zero
    (R : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
    (hpre : R.firstOrder < R.defect) :
    R.series.offDiag.coeff R.firstOrder ≠ 0 :=
  R.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre

end AdaptiveAlignedSmithCanonicalStationaryRankTwoGeometry

/-! ## Stationary endgame with no geometry erasure -/

/-- Geometry-preserving version of the stationary exact-clock endgame.

The four old repair-only exits are replaced by one typed rank-two geometry
constructor.  All closing and rigid alternatives are unchanged. -/
inductive AdaptiveAlignedSmithCanonicalExactClockStationaryGeometricEndgameOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | rankTwoGeometry
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (geometry : Nonempty
        (AdaptiveAlignedSmithCanonicalStationaryRankTwoGeometry (K := K) S))

  | schurClosing
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)

  | zeroSchurClosing
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)

  | planarRigidPacket
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigidPacket
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- **Stationary rank-two geometry extraction.**

This deliberately expands the two small places where the old local theorem
threw data away.  In the zero-Schur case we split the residual clock directly,
so the preterminal rank-one clock itself is retained. -/
theorem AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker.geometricExactClockEndgame
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (hclock :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hpos : 0 < S.blocker.aligned.endpoint.defect) :
    AdaptiveAlignedSmithCanonicalExactClockStationaryGeometricEndgameOutcome
      (K := K) s := by
  rcases S.blocker.exists_exactRightRecenteredHessianChart_or_allMinors with
    hchart | hall

  · let H := Classical.choice hchart
    rcases S.blocker.schur_or_zeroSchur_of_exactChart H hpos with
      hschur | hzero

    · let D := Classical.choice hschur
      rcases D.clock.firstOrder_preterminal_or_closing with hpre | hclose
      · exact .rankTwoGeometry S hclock
          ⟨.schurPreterminal D hpre⟩
      · exact .schurClosing S hclock hpos {
          source := S.blocker.recenteredSourceData
          chartData := D
          closing := ⟨hclose, D.clock.closing_transverse_nonzero hclose⟩
        }

    · let Z := Classical.choice hzero
      let E := Z.zeroData.toClock
      by_cases hres0 : E.residualDefect = 0
      · have hclose : HasAdaptiveAlignedZeroSchurClosing Z.zeroData := by
          left
          exact ⟨hres0, E.tail_constant_det_ne_zero_of_residual_zero hres0⟩
        exact .zeroSchurClosing S hclock hpos {
          source := S.blocker.recenteredSourceData
          chartData := Z
          closing := hclose
        }
      · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
        rcases E.tail_pivot_of_residual_pos hres with hleft | hright
        · let R := E.toRankOneClockLeft hres hleft
          rcases lt_or_eq_of_le R.firstOrder_le_defect with hpre | hclose
          · exact .rankTwoGeometry S hclock
              ⟨.zeroSchurPreterminal Z R hres rfl hpre⟩
          · have hclosing : HasAdaptiveAlignedZeroSchurClosing Z.zeroData := by
              right
              exact ⟨R, hres, rfl, hclose, by
                have h := R.series.transverse_nonzero_at_first R.hasTransverse
                have hfirst :
                    R.series.firstPositiveTransverseOrder R.hasTransverse =
                      R.defect := by
                  simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
                rw [hfirst] at h
                exact h⟩
            exact .zeroSchurClosing S hclock hpos {
              source := S.blocker.recenteredSourceData
              chartData := Z
              closing := hclosing
            }
        · let R := E.toRankOneClockRight hres hright
          rcases lt_or_eq_of_le R.firstOrder_le_defect with hpre | hclose
          · exact .rankTwoGeometry S hclock
              ⟨.zeroSchurPreterminal Z R hres rfl hpre⟩
          · have hclosing : HasAdaptiveAlignedZeroSchurClosing Z.zeroData := by
              right
              exact ⟨R, hres, rfl, hclose, by
                have h := R.series.transverse_nonzero_at_first R.hasTransverse
                have hfirst :
                    R.series.firstPositiveTransverseOrder R.hasTransverse =
                      R.defect := by
                  simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
                rw [hfirst] at h
                exact h⟩
            exact .zeroSchurClosing S hclock hpos {
              source := S.blocker.recenteredSourceData
              chartData := Z
              closing := hclosing
            }

  · rcases S.blocker.pureLongitudinal_or_quadraticPacket_of_allMinors hall with
      hpure | hplanar | hw

    · rcases S.blocker.pureLongitudinal_transverseFree_or_quadraticPacket
          hpure hall with hfree | hplanar' | hw'
      · exact (S.not_rawSpecialFiber_transverseFree hfree).elim
      · rcases hplanar' with ⟨P⟩
        cases P.localOutcome 0 with
        | rigid hrigid =>
            exact .planarRigidPacket S hclock hpos hall P hrigid
        | rankTwo hesc _hprogress =>
            exact .rankTwoGeometry S hclock ⟨.planarPacket P hesc⟩
      · rcases hw' with ⟨P⟩
        cases P.localOutcome 0 with
        | rigid hrigid =>
            exact .wSquareRigidPacket S hclock hpos hall P hrigid
        | rankTwo hesc _hprogress =>
            exact .rankTwoGeometry S hclock ⟨.wSquarePacket P hesc⟩

    · rcases hplanar with ⟨P⟩
      cases P.localOutcome 0 with
      | rigid hrigid =>
          exact .planarRigidPacket S hclock hpos hall P hrigid
      | rankTwo hesc _hprogress =>
          exact .rankTwoGeometry S hclock ⟨.planarPacket P hesc⟩

    · rcases hw with ⟨P⟩
      cases P.localOutcome 0 with
      | rigid hrigid =>
          exact .wSquareRigidPacket S hclock hpos hall P hrigid
      | rankTwo hesc _hprogress =>
          exact .rankTwoGeometry S hclock ⟨.wSquarePacket P hesc⟩

/-! ## Attach the justified repair promotion to the actual outer family -/

/-- A global rank-two promotion whose soundness payload is the stationary
geometry above.  The target may differ from the outer state only in its repair
coordinate, but unlike the legacy macro this change is justified by and stored
with actual family geometry. -/
structure AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  geometry :
    AdaptiveAlignedSmithCanonicalStationaryRankTwoGeometry (K := K) stationary
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target =
      (stationary.blocker.aligned.toOuterScaleAwareState s).withRepairOnly
        (rankTwoRepairState complexity)
  sourcePresentation :
    HasCertifiedRamifiedEpisodeInternalMove
      (stationary.blocker.aligned.toOuterScaleAwareState s) s
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target
      (stationary.blocker.aligned.toOuterScaleAwareState s)
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s

/-- Any retained stationary rank-two geometry canonically gives the justified
rank promotion on the actual aligned outer family. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hclock :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (G : AdaptiveAlignedSmithCanonicalStationaryRankTwoGeometry (K := K) S) :
    AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress
      RR s complexity := by
  let outer := S.blocker.aligned.toOuterScaleAwareState s
  let target := outer.withRepairOnly (rankTwoRepairState complexity)
  have houterRepair : outer.repair = rankOneRepairState complexity := by
    simpa [outer] using
      S.blocker.aligned.toOuterScaleAwareState_repair s |>.trans hsrepair
  have hrepair :
      RepairProgress outer.repair (rankTwoRepairState complexity) := by
    simpa [houterRepair] using rankOne_to_rankTwo_repairProgress complexity
  have hpresented : CertifiedSameScaleEpisodeProgress RR target outer := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    simpa [target, outer,
      ScaleAwareAdaptiveGeometricRestartState.withRepairOnly, hsrepair] using
      repairState_measure_lt_of_progress
        (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    stationary := S
    clock_eq := hclock
    geometry := G
    target := target
    target_eq := rfl
    sourcePresentation :=
      ⟨S.blocker.aligned.certifiedOuterInternal_of_defect_eq s hclock⟩
    presentedProgress := hpresented
    globalProgress := hglobal
  }

/-! ## Geometry-preserving reduced exact-clock dispatcher -/

/-- Parallel to the old reduced dispatcher, but the rank-two constructor now
carries its actual stationary geometry. -/
inductive AdaptiveAlignedSmithCanonicalExactClockGeometryReducedOutcome
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

  | schurClosing
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)

  | zeroSchurClosing
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)

  | planarRigidPacket
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigidPacket
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- The exact-clock dispatcher with all *stationary* repair-only rank-two
outputs eliminated. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockGeometryReducedDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockGeometryReducedOutcome
      RR s complexity := by
  rcases s.alignedSmithCanonicalExactClockDispatcher with
    hzero | ⟨target, hspend⟩ | ⟨S, hclock, hpos⟩ |
    ⟨W, hclock⟩ | ⟨B⟩

  · exact .zeroDefect hzero
  · exact .ramifiedSpend target hspend
  · cases S.geometricExactClockEndgame hclock hpos with
    | rankTwoGeometry S hclock hG =>
        rcases hG with ⟨G⟩
        exact .stationaryRankTwoProgress
          ⟨AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress.ofGeometry
            RR S complexity hsrepair hclock G⟩
    | schurClosing S _hclock _hpos C =>
        exact .schurClosing S C
    | zeroSchurClosing S _hclock _hpos C =>
        exact .zeroSchurClosing S C
    | planarRigidPacket S _hclock _hpos hall P hrigid =>
        exact .planarRigidPacket S hall P hrigid
    | wSquareRigidPacket S _hclock _hpos hall P hrigid =>
        exact .wSquareRigidPacket S hall P hrigid
  · exact .survivingExactClock W hclock
  · exact .sectionBoundaryInternal B

end

end HC4.Valuation
