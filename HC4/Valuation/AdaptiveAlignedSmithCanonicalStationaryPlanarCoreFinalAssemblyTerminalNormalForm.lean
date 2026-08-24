import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSlopeBridge
import Mathlib.Tactic

/-!
# Final assembly A6: terminal stationary-core normal form

A4 shows that every nonlinear transverse canonical-wall survivor is exactly
one-variable after a determinant-one binary source shear.  The only remaining
transverse constructor was the nominal low-degree branch `D ≤ 1`.

The stationary binary core retains a zero linear jet.  Hence its degree-one
ordinary homogeneous component is identically zero.  Since the maximal
homogeneous component in the low-degree constructor is nonzero, `D = 1` is
impossible and therefore `D = 0`.

Thus the canonical transverse wall has now collapsed to exactly two terminal
forms:

* a genuine degree-zero endpoint; or
* an exact nonlinear one-variable endpoint after source shear.

The A5 zero-Schur source-ready packet is transported unchanged.
No progress assertion and no additional hypothesis is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The nominal `D ≤ 1` binary stationary survivor is actually degree zero:
the alternative `D = 1` would make its nonzero top homogeneous component equal
to the zero linear component of the retained zero jet. -/
theorem binaryStationaryLowDegree_zeroJet_forces_degree_zero
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ) (H : MvPolynomial (Fin 2) K)
    (hD : D ≤ 1)
    (H_eq : H = binaryOrdinaryDegreeComponent Q D)
    (H_ne_zero : H ≠ 0)
    (hlinear : ∀ i : Fin 2,
      MvPolynomial.coeff (Finsupp.single i 1) Q = 0) :
    D = 0 := by
  by_contra hD0
  have hD1 : D = 1 := by omega
  apply H_ne_zero
  rw [H_eq, hD1]
  ext d
  by_cases hdeg : d.degree = 1
  · have hsum : d 0 + d 1 = 1 := by
      rw [← finTwo_degree_eq_add_curved d]
      exact hdeg
    have hcases :
        (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by
      omega
    rcases hcases with h | h
    · have hd : d = Finsupp.single 0 1 := by
        apply Finsupp.ext
        intro k
        fin_cases k <;> simp [h.1, h.2, Finsupp.single_apply]
      rw [coeff_binaryOrdinaryDegreeComponent_of_degree_curved Q d 1 hdeg,
        hd, hlinear 0]
      simp
    · have hd : d = Finsupp.single 1 1 := by
        apply Finsupp.ext
        intro k
        fin_cases k <;> simp [h.1, h.2, Finsupp.single_apply]
      rw [coeff_binaryOrdinaryDegreeComponent_of_degree_curved Q d 1 hdeg,
        hd, hlinear 1]
      simp
  · unfold binaryOrdinaryDegreeComponent
    rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree]
    have hcast : (d.degree : ℤ) ≠ (1 : ℤ) := by
      exact_mod_cast hdeg
    simp [hcast]

/-- A6 global frontier.  Relative to A5, the only change is that the nominal
low-degree transverse constructor has been sharpened from `D ≤ 1` to the
literal degree-zero component. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreTerminalNormalFormOutcome
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
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | earlySchurRS2Ready
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

  | canonicalWallLongitudinal
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
      (face_ne_zero : face ≠ 0)
      (base_support :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.IsLongitudinalBaseSupport face)
      (source_collision :
        HasExactGradientCollision
          (polynomialFamilySpecialFiber D.family)
          (fun _ : Fin 4 => (0 : K))
          (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i))
      (face_linear_zero :
        ∀ i : Fin 4,
          MvPolynomial.coeff (Finsupp.single i 1) face = 0)

  | canonicalWallTransverseDegreeZero
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (H : MvPolynomial (Fin 2) K)
      (H_eq : H = binaryOrdinaryDegreeComponent data.binaryFace 0)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ data.binaryFace.support, d.degree ≤ 0)

  | canonicalWallTransverseNonlinearAxis
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (straight : BinarySingularHessianNonlinearAxisStraighteningData data.binaryFace)

  | zeroSchurSourceReady
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)

  | planarRigid
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
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigid
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
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | sectionGaugeKilled
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hkilled :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)

  | sectionGaugeOrderRaised
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hnew :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index)
            hnew)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- A6 assembly theorem: the zero linear jet removes the last degree-one
transverse stationary endpoint. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreTerminalNormalFormFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreTerminalNormalFormOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreZeroSlopeBridgedAssemblyFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurRS2Ready S clock_eq clock_pos C hlt htangential R
  | canonicalWallLongitudinal S clock_eq clock_pos C heq D face face_ne_zero
      base_support source_collision face_linear_zero =>
      exact .canonicalWallLongitudinal S clock_eq clock_pos C heq D face
        face_ne_zero base_support source_collision face_linear_zero
  | canonicalWallTransverseLowDegree S clock_eq clock_pos C heq data D H hD
      H_eq H_ne_zero maximal =>
      have hD0 := binaryStationaryLowDegree_zeroJet_forces_degree_zero
        data.binaryFace D H hD H_eq H_ne_zero data.binaryFace_linear_zero
      subst D
      exact .canonicalWallTransverseDegreeZero S clock_eq clock_pos C heq data
        H H_eq H_ne_zero maximal
  | canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq data straight =>
      exact .canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq
        data straight
  | zeroSchurSourceReady S clock_eq clock_pos C source =>
      exact .zeroSchurSourceReady S clock_eq clock_pos C source
  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .planarRigid S clock_eq clock_pos hall P hrigid
  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .wSquareRigid S clock_eq clock_pos hall P hrigid
  | sectionGaugeKilled S clock_eq clock_pos C heq G hkilled =>
      exact .sectionGaugeKilled S clock_eq clock_pos C heq G hkilled
  | sectionGaugeOrderRaised S clock_eq clock_pos C heq G hnew hstrict =>
      exact .sectionGaugeOrderRaised S clock_eq clock_pos C heq G hnew hstrict
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace

end

end HC4.Valuation
