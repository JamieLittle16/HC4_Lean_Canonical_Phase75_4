import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCore
import Mathlib.Tactic

/-!
# Zero-jet elimination of affine stationary wall tails

The stationary planar-core split still retained two `m = 1` canonical-wall
constructors whose faces were supported only on pure complementary linear
monomials.  Those constructors are incompatible with the honest aligned
square source.

The aligned square source now retains the zero source jet of the right-
recentered family through both the longitudinal identity chart and the honest
three-transvection transverse alignment.  Therefore every source-linear
coefficient of its special fibre vanishes.  A nonzero exact initial face
supported entirely on pure linear monomials is impossible.

Consequently the canonical-wall stationary contribution contains only the
genuine `m = 0` one- or two-variable nonlinear core.  No JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The longitudinal `m = 1` affine wall tail contradicts the retained zero
linear source jet of the aligned square special fibre. -/
theorem longitudinalAffineTail_impossible
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (face : MvPolynomial (Fin 4) K)
    (face_eq :
      face = Polynomial.initialForm pureLongitudinalTransverseWeight (-1)
        (polynomialFamilySpecialFiber D.family))
    (face_ne_zero : face ≠ 0)
    (pure_affine : IsLongitudinalPureAffineSupport face) :
    False := by
  rcases MvPolynomial.support_nonempty.mpr face_ne_zero with ⟨d, hd⟩
  rcases pure_affine d hd with ⟨i, hi0, hdi⟩
  subst d
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single i 1) face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [face_eq, HC4.Polynomial.coeff_initialForm] at hcoeff
  have hzero := D.specialFiber_linearCoeff_zero i
  simp [hzero] at hcoeff

/-- The transverse `m = 1` affine wall tail likewise contradicts the retained
zero linear source jet. -/
theorem transverseAffineTail_impossible
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (face : MvPolynomial (Fin 4) K)
    (face_eq :
      face = Polynomial.initialForm
        (directClosingTransverseComplementWeight D.index) (-1)
        (polynomialFamilySpecialFiber D.family))
    (face_ne_zero : face ≠ 0)
    (pure_affine : IsTransversePureAffineSupport D.index face) :
    False := by
  rcases MvPolynomial.support_nonempty.mpr face_ne_zero with ⟨d, hd⟩
  rcases pure_affine d hd with ⟨i, hi0, hiindex, hdi⟩
  subst d
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single i 1) face ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [face_eq, HC4.Polynomial.coeff_initialForm] at hcoeff
  have hzero := D.specialFiber_linearCoeff_zero i
  simp [hzero] at hcoeff

/-- The genuine stationary canonical-wall core after zero-jet elimination.
Only complementary degree zero survives. -/
inductive DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinalCore
      (D : DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm pureLongitudinalTransverseWeight 0
          (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (base_support : IsLongitudinalBaseSupport face)

  | transverseCore
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm
          (directClosingTransverseComplementWeight D.index) 0
          (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (base_support : IsTransverseBaseSupport D.index face)
      (base_det_zero :
        binaryDirectionalHessianDet (0 : Fin 4) D.index face = 0)

/-- The four-way planar-core split collapses unconditionally to its two
`m = 0` nonlinear constructors. -/
theorem DirectClosingCanonicalSquareStationaryPlanarCoreData.toZeroJetPlanarCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareStationaryPlanarCoreData C heq) :
    DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData C heq := by
  cases L with
  | longitudinalCore D face face_eq face_ne_zero base_support =>
      exact .longitudinalCore D face face_eq face_ne_zero base_support
  | transverseCore D hindex face face_eq face_ne_zero base_support base_det_zero =>
      exact .transverseCore D hindex face face_eq face_ne_zero base_support base_det_zero
  | longitudinalAffineTail D face face_eq face_ne_zero pure_affine hessian_zero =>
      exact False.elim
        (longitudinalAffineTail_impossible D face face_eq face_ne_zero pure_affine)
  | transverseAffineTail D hindex face face_eq face_ne_zero pure_affine hessian_zero =>
      exact False.elim
        (transverseAffineTail_impossible D face face_eq face_ne_zero pure_affine)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Zero-jet strengthened common stationary packet -/

/-- The common stationary packet after the canonical-wall affine tails have
been removed by retained zero-jet provenance. -/
inductive AdaptiveAlignedSmithCanonicalZeroJetStationaryPlanarCorePacket
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | earlySchurConstantRS2
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : Nonempty C.ConstantSpecialSchurKernelLineRS2PreassemblyData)

  | canonicalWall
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (L : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareZeroJetStationaryPlanarCoreData
        C heq)

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

/-- Remove the impossible affine wall tails from the already-unified
stationary planar-core packet. -/
theorem AdaptiveAlignedSmithCanonicalStationaryPlanarCorePacket.toZeroJetPlanarCorePacket
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalStationaryPlanarCorePacket s) :
    AdaptiveAlignedSmithCanonicalZeroJetStationaryPlanarCorePacket s := by
  cases P with
  | earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R
  | canonicalWall S clock_eq clock_pos C heq L =>
      exact .canonicalWall S clock_eq clock_pos C heq L.toZeroJetPlanarCore
  | zeroSchur S clock_eq clock_pos C =>
      exact .zeroSchur S clock_eq clock_pos C
  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .planarRigid S clock_eq clock_pos hall P hrigid
  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .wSquareRigid S clock_eq clock_pos hall P hrigid

/-- Assembly-facing convergence outcome with the canonical wall already
reduced to its genuine zero-jet planar core. -/
inductive AdaptiveAlignedSmithCanonicalZeroJetPlanarCoreOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | stationary
      (P : AdaptiveAlignedSmithCanonicalZeroJetStationaryPlanarCorePacket s)

  | sectionGauge
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)

  | survivingExactClock
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- Refine the current exact-clock convergence frontier without adding a new
branch: stationary canonical walls are now genuine `m = 0` planar cores. -/
theorem AdaptiveAlignedSmithCanonicalPlanarAffineConvergenceOutcome.toZeroJetPlanarCoreOutcome
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {RR : RepairRanking}
    {complexity : ℕ}
    (O : AdaptiveAlignedSmithCanonicalPlanarAffineConvergenceOutcome RR s complexity) :
    AdaptiveAlignedSmithCanonicalZeroJetPlanarCoreOutcome RR s complexity := by
  cases O with
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | stationary P =>
      have P' := P.toStationaryPlanarCorePacket
      exact .stationary P'.toZeroJetPlanarCorePacket
  | sectionGauge S clock_eq clock_pos C heq G =>
      exact .sectionGauge S clock_eq clock_pos C heq G
  | survivingExactClock W clock_eq =>
      exact .survivingExactClock W clock_eq
  | sectionBoundaryInternal B =>
      exact .sectionBoundaryInternal B

end

end HC4.Valuation
