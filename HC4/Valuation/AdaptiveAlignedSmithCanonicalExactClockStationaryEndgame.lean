import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockDispatcher
import HC4.Valuation.AdaptiveAlignedSmithClosingChartProvenance
import HC4.Valuation.AdaptiveAlignedSmithCanonicalSoundEpisodeInterface
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalFirstWall
import Mathlib.Tactic

/-!
# Exact-clock stationary blocker endgame

The scale-sound exact-clock dispatcher leaves a canonical blocker only after
all positive saturated rational transverse slopes have been exhausted.  Such a
stationary blocker has actual transverse support on the honest right-recentered
special fibre in each of the three transverse coordinates.

This observation removes one branch of the older blocker endgame completely.
The `pureLongitudinal_transverseFree` alternative cannot occur: longitudinal
right recentering preserves projected Smith support exactly, whereas a
transverse-free raw special fibre has projected support only at transverse
exponent `(0,0,0)`.

We then rerun the chart-provenance endgame.  Rank-one -> rank-two repair is
consumed soundly as

    exact outer ramification (zero cost) ; same-scale repair descent,

and the only local geometric outputs left are the two honest closing charts
and the two rigid packet geometries.  No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## A scale-aware repair-only presentation -/

/-- Change only the finite repair coordinate of a scale-aware state. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.withRepairOnly
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (repair : RepairState) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) where
  rawDefect := s.rawDefect
  scale := s.scale
  scale_pos := s.scale_pos
  degreeCap := s.degreeCap
  sourceComplexity := s.sourceComplexity
  repair := repair
  family := s.family
  movingSection := s.movingSection
  hessianDefect := s.hessianDefect
  nonlinearDegreeBound := s.nonlinearDegreeBound
  exactCollision := s.exactCollision
  sectionSpecial := s.sectionSpecial

@[simp] theorem ScaleAwareAdaptiveGeometricRestartState.withRepairOnly_rawDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (repair : RepairState) :
    (s.withRepairOnly repair).rawDefect = s.rawDefect := rfl

@[simp] theorem ScaleAwareAdaptiveGeometricRestartState.withRepairOnly_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (repair : RepairState) :
    (s.withRepairOnly repair).scale = s.scale := rfl

@[simp] theorem ScaleAwareAdaptiveGeometricRestartState.withRepairOnly_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (repair : RepairState) :
    (s.withRepairOnly repair).repair = repair := rfl

/-! ## Stationarity rules out complete transverse freeness -/

namespace AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-- A stationary blocker cannot have a raw special fibre free of all three
transverse variables.

The right-recentered special fibre has a monomial using coordinate `3` by the
all-transverse zero-rational-slope normal form.  Its Smith projection therefore
has positive `d` coordinate.  Projected Smith support is unchanged by
longitudinal recentering, contradicting transverse freeness of the raw fibre. -/
theorem not_rawSpecialFiber_transverseFree
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    ¬ (∀ d ∈ S.blocker.aligned.endpoint.rawSpecialFiber.support,
        d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0) := by
  intro hfree
  rcases S.specialFiber_witnesses.2.2 with ⟨d, hd, hd3⟩
  have hproj :
      smithSupportExponentOf (1 : Fin 4) 2 3 d ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          S.blocker.aligned.endpoint.rawSpecialFiber := by
    have hprojRec :=
      smithSupportExponentOf_mem_projectedSupport
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily) d hd
    rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber,
      smithProjectedSupport_longitudinalRightRecenterHom] at hprojRec
    exact hprojRec
  classical
  unfold smithProjectedSupport at hproj
  rcases Finset.mem_image.mp hproj with ⟨d', hd', heq⟩
  have hfree' := hfree d' hd'
  have hcoord : d' (3 : Fin 4) = d (3 : Fin 4) := by
    simpa [smithSupportExponentOf] using congrArg SmithSupportExponent.d heq
  rw [hfree'.2.2] at hcoord
  omega

end AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-! ## Sound exact-clock rank-two repair macro -/

/-- At an exact aligned outer clock, rank-one -> rank-two repair is a sound
macro step: first the exact `20`-fold ramified presentation, then a genuine
same-scale repair descent. -/
theorem AdaptiveAlignedSmithMinimalZeroJetEndpoint.exists_outerRankTwoRepairMacro
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (E : AdaptiveAlignedSmithMinimalZeroJetEndpoint (K := K) s.degreeCap)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hclock :
      E.endpoint.defect = alignedSmithRamificationIndex * s.rawDefect)
    (hrepair :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity)) :
    ∃ outer target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      HasCertifiedRamifiedEpisodeInternalMove outer s ∧
      CertifiedSameScaleEpisodeProgress RR target outer := by
  let outer := E.toOuterScaleAwareState s
  let target := outer.withRepairOnly (rankTwoRepairState complexity)
  refine ⟨outer, target, ⟨E.certifiedOuterInternal_of_defect_eq s hclock⟩, ?_⟩
  apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
  · rfl
  · rfl
  · simpa [outer, target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly,
      AdaptiveAlignedSmithMinimalZeroJetEndpoint.toOuterScaleAwareState,
      hsrepair] using hrepair

/-! ## The reduced exact-clock stationary endgame -/

/-- Local blocker geometry after stationarity has removed the transverse-free
branch and every rank-two repair has been converted into a sound macro step. -/
inductive AdaptiveAlignedSmithCanonicalExactClockStationaryEndgameOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : CertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

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
      (h : HasRigidRankOnePacket
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
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

namespace AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-- **Stationary exact-clock blocker endgame.**

At positive exact outer clock, every stationary blocker is either already a
sound rank-two repair macro, an honest rank-one/zero-Schur closing source with
its exact chart, or one of the two rigid packet geometries.  Complete
transverse freeness has disappeared by stationarity. -/
theorem exactClockEndgame
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (hclock :
      S.blocker.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hpos : 0 < S.blocker.aligned.endpoint.defect) :
    AdaptiveAlignedSmithCanonicalExactClockStationaryEndgameOutcome
      RR s complexity := by
  rcases S.blocker.chartFrontier complexity hpos with
    hrepair | ⟨D, hclose⟩ | ⟨Z, hclose⟩ | hall

  · rcases
      S.blocker.aligned.exists_outerRankTwoRepairMacro
        RR s complexity hsrepair hclock hrepair with
      ⟨outer, target, hmove, hprogress⟩
    rcases hmove with ⟨hmove⟩
    exact .rankTwoMacro outer target hmove hprogress

  · exact .schurClosing S hclock hpos {
      source := S.blocker.recenteredSourceData
      chartData := D
      closing := hclose
    }

  · exact .zeroSchurClosing S hclock hpos {
      source := S.blocker.recenteredSourceData
      chartData := Z
      closing := hclose
    }

  · rcases S.blocker.pureLongitudinal_or_quadraticPacket_of_allMinors hall with
      hpure | hplanar | hw

    · rcases S.blocker.pureLongitudinal_transverseFree_or_quadraticPacket
          hpure hall with hfree | hplanar' | hw'
      · exact (S.not_rawSpecialFiber_transverseFree hfree).elim
      · rcases hplanar' with ⟨P⟩
        rcases P.localOutcome complexity with hrigid | ⟨_hesc, hrepair⟩
        · exact .planarRigidPacket S hclock hpos hall P hrigid
        · rcases
            S.blocker.aligned.exists_outerRankTwoRepairMacro
              RR s complexity hsrepair hclock hrepair with
            ⟨outer, target, hmove, hprogress⟩
          rcases hmove with ⟨hmove⟩
          exact .rankTwoMacro outer target hmove hprogress
      · rcases hw' with ⟨P⟩
        rcases P.localOutcome complexity with hrigid | ⟨_hesc, hrepair⟩
        · exact .wSquareRigidPacket S hclock hpos hall P hrigid
        · rcases
            S.blocker.aligned.exists_outerRankTwoRepairMacro
              RR s complexity hsrepair hclock hrepair with
            ⟨outer, target, hmove, hprogress⟩
          rcases hmove with ⟨hmove⟩
          exact .rankTwoMacro outer target hmove hprogress

    · rcases hplanar with ⟨P⟩
      rcases P.localOutcome complexity with hrigid | ⟨_hesc, hrepair⟩
      · exact .planarRigidPacket S hclock hpos hall P hrigid
      · rcases
          S.blocker.aligned.exists_outerRankTwoRepairMacro
            RR s complexity hsrepair hclock hrepair with
          ⟨outer, target, hmove, hprogress⟩
        rcases hmove with ⟨hmove⟩
        exact .rankTwoMacro outer target hmove hprogress

    · rcases hw with ⟨P⟩
      rcases P.localOutcome complexity with hrigid | ⟨_hesc, hrepair⟩
      · exact .wSquareRigidPacket S hclock hpos hall P hrigid
      · rcases
          S.blocker.aligned.exists_outerRankTwoRepairMacro
            RR s complexity hsrepair hclock hrepair with
          ⟨outer, target, hmove, hprogress⟩
        rcases hmove with ⟨hmove⟩
        exact .rankTwoMacro outer target hmove hprogress

end AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-! ## Global reduced exact-clock dispatcher -/

/-- Global exact-clock frontier after the stationary blocker's transverse-free
branch and all rank-two repair exits have been consumed soundly.

The only blocker-side local geometries still visible are the two honest Schur
closing sources and the two rigid packet certificates. -/
inductive AdaptiveAlignedSmithCanonicalExactClockReducedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : CertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

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

/-- **Reduced exact-clock canonical dispatcher at the rank-one repair stage.**

This theorem runs the exact-clock outer classifier and immediately reruns the
stationary blocker endgame in the provenance-preserving chart presentation.
The old transverse-free strict-successor constructor cannot occur under the
stationary hypothesis, while every rank-two repair is returned as a sound
ramified-internal-then-same-scale-strict macro. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockReducedDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockReducedOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalExactClockDispatcher with
    hzero | ⟨target, hspend⟩ | ⟨S, hclock, hpos⟩ |
    ⟨W, hclock⟩ | ⟨B⟩

  · exact .zeroDefect hzero

  · exact .ramifiedSpend target hspend

  · rcases S.exactClockEndgame RR complexity hsrepair hclock hpos with
      ⟨outer, target, hmove, hprogress⟩ |
      ⟨S, _hclockS, _hposS, C⟩ | ⟨S, _hclockS, _hposS, C⟩ |
      ⟨S, _hclockS, _hposS, hall, P, hrigid⟩ |
      ⟨S, _hclockS, _hposS, hall, P, hrigid⟩
    · exact .rankTwoMacro outer target hmove hprogress
    · exact .schurClosing S C
    · exact .zeroSchurClosing S C
    · exact .planarRigidPacket S hall P hrigid
    · exact .wSquareRigidPacket S hall P hrigid

  · exact .survivingExactClock W hclock

  · exact .sectionBoundaryInternal B

end

end HC4.Valuation
