import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblySourceRefinement
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreCurvedElimination
import Mathlib.Tactic

/-!
# Final assembly A4: exact binary axis straightening

A3 exposes the canonical transverse stationary wall together with the curved-
free binary Hessian frontier.  The nonlinear constructors in that frontier
still look different because they remember how much of the lower staircase
has already been exposed.

For final assembly this distinction is unnecessary.  The first-contact
rigidity theorem proved in `...CurvedElimination` is stronger: once the
nonlinear top homogeneous layer is a power of one linear form, a determinant-
one binary shear makes that top layer a pure coordinate power, and singular
Hessian plus the zero linear jet forbids *any* support off the same axis.

Thus all nonlinear canonical transverse survivors are literally one-variable
after an honest source shear.  This file packages that fact once and folds the
three nonlinear A3 constructors into one exact axis-straightened certificate.
No recursive progress is asserted here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Exact orientation of a nonlinear singular-Hessian binary polynomial after
straightening its top linear form.

If the first coefficient of the top line vanishes, the polynomial was already
supported on coordinate `1`.  Otherwise the determinant-one shear
`X₀ ↦ X₀ - (c₁/c₀) X₁` makes the whole polynomial supported on coordinate
`0`. -/
inductive BinarySingularHessianAxisOrientation
    (Q : MvPolynomial (Fin 2) K)
    (c : Fin 2 → K) : Type (u + 1)

  | axisOne
      (hc0 : c 0 = 0)
      (hc1 : c 1 ≠ 0)
      (line_eq :
        gradientRatioLinearForm c =
          MvPolynomial.C (c 1) * MvPolynomial.X 1)
      (noOutside : ¬ (binaryOutsideSupport (0 : Fin 2) Q).Nonempty)

  | axisZeroAfterShear
      (hc0 : c 0 ≠ 0)
      (t : K)
      (line_eq :
        binarySourceShearHom t (gradientRatioLinearForm c) =
          MvPolynomial.C (c 0) * MvPolynomial.X 0)
      (noOutside :
        ¬ (binaryOutsideSupport (1 : Fin 2)
          (binarySourceShearHom t Q)).Nonempty)

/-- Common nonlinear data after the binary stationary wall has been reduced to
one exact axis. -/
structure BinarySingularHessianNonlinearAxisStraighteningData
    (Q : MvPolynomial (Fin 2) K) where
  D : ℕ
  H : MvPolynomial (Fin 2) K
  hD : 2 ≤ D
  H_eq : H = binaryOrdinaryDegreeComponent Q D
  H_ne_zero : H ≠ 0
  maximal : ∀ d ∈ Q.support, d.degree ≤ D
  a : K
  c : Fin 2 → K
  normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D
  orientation : BinarySingularHessianAxisOrientation Q c

/-- **Binary-to-one-variable straightening adapter.**

This is the assembly form of the finite first-contact theorem already proved
inside curved elimination.  It does not use the next layer at all: every
nonlinear singular-Hessian binary polynomial with zero linear jet and top
homogeneous power `a L^D` is supported on a single axis after the canonical
binary source shear. -/
noncomputable def binarySingularHessian_nonlinearAxisStraightening
    (Q : MvPolynomial (Fin 2) K)
    (D : ℕ) (H : MvPolynomial (Fin 2) K)
    (hD : 2 ≤ D)
    (H_eq : H = binaryOrdinaryDegreeComponent Q D)
    (H_ne_zero : H ≠ 0)
    (maximal : ∀ d ∈ Q.support, d.degree ≤ D)
    (a : K) (c : Fin 2 → K)
    (normalForm : H = MvPolynomial.C a * (gradientRatioLinearForm c) ^ D)
    (hlinear : ∀ i : Fin 2,
      MvPolynomial.coeff (Finsupp.single i 1) Q = 0)
    (hdet : binaryDirectionalHessianDet (0 : Fin 2) 1 Q = 0) :
    BinarySingularHessianNonlinearAxisStraighteningData Q := by
  have ha : a ≠ 0 := by
    intro ha0
    apply H_ne_zero
    rw [normalForm, ha0]
    simp
  have hcNonzero : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    apply H_ne_zero
    rw [normalForm]
    have hL : gradientRatioLinearForm c = 0 := by
      classical
      unfold gradientRatioLinearForm
      rw [Fin.sum_univ_two]
      simp [hnot.1, hnot.2]
    rw [hL]
    have hD0 : D ≠ 0 := by omega
    simp [hD0]

  refine {
    D := D
    H := H
    hD := hD
    H_eq := H_eq
    H_ne_zero := H_ne_zero
    maximal := maximal
    a := a
    c := c
    normalForm := normalForm
    orientation := ?_
  }

  by_cases hc0 : c 0 = 0
  · have hc1 : c 1 ≠ 0 := by
      rcases hcNonzero with h | h
      · exact (h hc0).elim
      · exact h
    have hL : gradientRatioLinearForm c =
        MvPolynomial.C (c 1) * MvPolynomial.X 1 := by
      classical
      unfold gradientRatioLinearForm
      rw [Fin.sum_univ_two]
      simp [hc0]
    have hHaxis : H =
        MvPolynomial.C (a * (c 1) ^ D) * (MvPolynomial.X 1) ^ D := by
      rw [normalForm, hL, mul_pow, ← MvPolynomial.C_pow, ← mul_assoc,
        ← MvPolynomial.C_mul]
    have htopCoeff :
        MvPolynomial.coeff (Finsupp.single (1 : Fin 2) D) Q ≠ 0 := by
      let dtop : Fin 2 →₀ ℕ := Finsupp.single (1 : Fin 2) D
      have hd : dtop.degree = D := by
        dsimp [dtop]
        rw [finTwo_degree_eq_add_curved]
        simp [Finsupp.single_apply]
      have hcH : MvPolynomial.coeff dtop H = MvPolynomial.coeff dtop Q := by
        rw [H_eq]
        exact coeff_binaryOrdinaryDegreeComponent_of_degree_curved Q dtop D hd
      have hleft : MvPolynomial.coeff dtop H = a * c 1 ^ D := by
        rw [hHaxis]
        dsimp [dtop]
        rw [MvPolynomial.C_mul_X_pow_eq_monomial]
        simp
      have hscalar : a * c 1 ^ D ≠ 0 := mul_ne_zero ha (pow_ne_zero D hc1)
      intro hz
      apply hscalar
      rw [← hleft, hcH, hz]
    have htopFacet :
        ∀ d ∈ Q.support, d.degree = D → d (0 : Fin 2) = 0 := by
      intro d hd hddeg
      have hcoeff : MvPolynomial.coeff d H ≠ 0 := by
        rw [H_eq]
        unfold binaryOrdinaryDegreeComponent
        rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree, hddeg]
        simp [MvPolynomial.mem_support_iff.mp hd]
      rw [hHaxis] at hcoeff
      have hpderiv : MvPolynomial.pderiv (0 : Fin 2)
          (MvPolynomial.C (a * c 1 ^ D) * (MvPolynomial.X 1) ^ D) = 0 := by
        simp
      exact exponent_eq_zero_of_pderiv_eq_zero 0 _ hpderiv d hcoeff
    have hno := binarySingularHessian_no_outsideSupport_of_pureTop
      Q D 1 0 (by decide) hD maximal htopFacet htopCoeff (hlinear 0) hdet
    exact .axisOne hc0 hc1 hL hno

  · let t : K := -(c 1 / c 0)
    let Qs := binarySourceShearHom t Q
    have hdetS : binaryDirectionalHessianDet (0 : Fin 2) 1 Qs = 0 := by
      dsimp [Qs, t]
      rw [binaryDirectionalHessianDet_binarySourceShearHom, hdet]
      simp
    have hHsComp :
        binaryOrdinaryDegreeComponent Qs D =
          MvPolynomial.C (a * (c 0) ^ D) * (MvPolynomial.X 0) ^ D := by
      have hmap := congrArg (binarySourceShearHom t) H_eq
      rw [binarySourceShearHom_binaryOrdinaryDegreeComponent] at hmap
      have haxis := binarySourceShearHom_gradientRatioLinearForm_axis c hc0
      dsimp [t] at hmap haxis
      rw [normalForm, map_mul, map_pow, binarySourceShearHom_C, haxis] at hmap
      rw [← hmap]
      rw [mul_pow, ← MvPolynomial.C_pow, ← mul_assoc, ← MvPolynomial.C_mul]
    have htopCoeffS :
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) D) Qs ≠ 0 := by
      let dtop : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) D
      have hd : dtop.degree = D := by
        dsimp [dtop]
        rw [finTwo_degree_eq_add_curved]
        simp [Finsupp.single_apply]
      have hcComp : MvPolynomial.coeff dtop
          (binaryOrdinaryDegreeComponent Qs D) = MvPolynomial.coeff dtop Qs :=
        coeff_binaryOrdinaryDegreeComponent_of_degree_curved Qs dtop D hd
      have hright : MvPolynomial.coeff dtop
          (MvPolynomial.C (a * c 0 ^ D) * MvPolynomial.X 0 ^ D) =
          a * c 0 ^ D := by
        dsimp [dtop]
        rw [MvPolynomial.C_mul_X_pow_eq_monomial]
        simp
      have hscalar : a * c 0 ^ D ≠ 0 := mul_ne_zero ha (pow_ne_zero D hc0)
      intro hz
      apply hscalar
      rw [← hright, ← hHsComp, hcComp, hz]
    have htopFacetS :
        ∀ d ∈ Qs.support, d.degree = D → d (1 : Fin 2) = 0 := by
      intro d hd hddeg
      have hcoeff : MvPolynomial.coeff d
          (binaryOrdinaryDegreeComponent Qs D) ≠ 0 := by
        unfold binaryOrdinaryDegreeComponent
        rw [coeff_initialForm, binaryOrdinaryIntegerWeight_eq_degree, hddeg]
        simp [MvPolynomial.mem_support_iff.mp hd]
      rw [hHsComp] at hcoeff
      have hpderiv : MvPolynomial.pderiv (1 : Fin 2)
          (MvPolynomial.C (a * c 0 ^ D) * (MvPolynomial.X 0) ^ D) = 0 := by
        simp
      exact exponent_eq_zero_of_pderiv_eq_zero 1 _ hpderiv d hcoeff
    have hmaxS : ∀ d ∈ Qs.support, d.degree ≤ D := by
      dsimp [Qs]
      exact binarySourceShearHom_support_degree_le t Q D maximal
    have hlinearS := binarySourceShearHom_linearCoeff_zero t Q hlinear
    have hno := binarySingularHessian_no_outsideSupport_of_pureTop
      Qs D 0 1 (by decide) hD hmaxS htopFacetS htopCoeffS
        (hlinearS 1) hdetS
    have haxis := binarySourceShearHom_gradientRatioLinearForm_axis c hc0
    exact .axisZeroAfterShear hc0 t (by simpa [t] using haxis) hno

/-- A4 global frontier.  The three nonlinear curved-free transverse
constructors have collapsed to one exact one-variable source certificate. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreAxisStraightenedAssemblyOutcome
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

  | canonicalWallTransverseLowDegree
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (data : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareBinaryStationaryCoreData C heq)
      (D : ℕ) (H : MvPolynomial (Fin 2) K)
      (hD : D ≤ 1)
      (H_eq : H = binaryOrdinaryDegreeComponent data.binaryFace D)
      (H_ne_zero : H ≠ 0)
      (maximal : ∀ d ∈ data.binaryFace.support, d.degree ≤ D)

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

  | zeroSchur
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)

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

/-- A4 assembly theorem: run the nonlinear binary straightening immediately on
every canonical transverse survivor. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreAxisStraightenedAssemblyFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreAxisStraightenedAssemblyOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreSourceRefinedAssemblyFrontier
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
  | canonicalWallTransverse S clock_eq clock_pos C heq data frontier =>
      cases frontier with
      | lowDegree D H hD H_eq H_ne_zero maximal =>
          exact .canonicalWallTransverseLowDegree S clock_eq clock_pos C heq
            data D H hD H_eq H_ne_zero maximal
      | nonlinearCollapsed D H hD H_eq H_ne_zero maximal a c normalForm Q_eq_H =>
          let straight := binarySingularHessian_nonlinearAxisStraightening
            data.binaryFace D H hD H_eq H_ne_zero maximal a c normalForm
            data.binaryFace_linear_zero data.binary_det_zero
          exact .canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq
            data straight
      | nonlinearNextAffine D H hD H_eq H_ne_zero maximal a c normalForm
          R R_eq R_ne_zero E G E_lt_D E_le_one G_eq G_ne_zero remainder_maximal
          G_homogeneous transverse_sq_zero =>
          let straight := binarySingularHessian_nonlinearAxisStraightening
            data.binaryFace D H hD H_eq H_ne_zero maximal a c normalForm
            data.binaryFace_linear_zero data.binary_det_zero
          exact .canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq
            data straight
      | nonlinearNextLocked D H hD H_eq H_ne_zero maximal a c normalForm
          R R_eq R_ne_zero E G E_lt_D E_ge_two G_eq G_ne_zero remainder_maximal
          G_homogeneous transverse_sq_zero transverse_first_zero =>
          let straight := binarySingularHessian_nonlinearAxisStraightening
            data.binaryFace D H hD H_eq H_ne_zero maximal a c normalForm
            data.binaryFace_linear_zero data.binary_det_zero
          exact .canonicalWallTransverseNonlinearAxis S clock_eq clock_pos C heq
            data straight
  | zeroSchur S clock_eq clock_pos C =>
      exact .zeroSchur S clock_eq clock_pos C
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
