import HC4.Valuation.AdaptiveAlignedSmithCanonicalLowDimensionalStationaryConvergence
import Mathlib.Tactic

/-!
# Literal planar-affine normal form for the converged stationary wall face

The previous convergence theorem shows that every surviving canonical-square
wall face has Hessian support on either the marked longitudinal axis or on one
base plane `(0, ell)`, and that every complementary gradient component is a
scalar polynomial.

This file upgrades that derivative statement to an exact support statement.
If `pderiv i F` is constant and a supported monomial of `F` actually contains
`X_i`, then that monomial is *exactly* `X_i`: no base monomial can multiply it
and the exponent of `X_i` is one.  Consequently a surviving wall face is
literally a base polynomial plus pure affine coordinate monomials in the
complementary variables.

The result is packaged back into the stationary convergence frontier.  No
terminal extraction and no JC2 hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- If one partial derivative is constant, then every supported monomial
which contains that variable is the pure linear monomial in that variable. -/
theorem support_eq_single_of_pderiv_eq_C_of_pos
    (F : MvPolynomial (Fin 4) K)
    (i : Fin 4)
    (c : K)
    (hderiv : MvPolynomial.pderiv i F = MvPolynomial.C c)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ F.support)
    (hdi : 0 < d i) :
    d = Finsupp.single i 1 := by
  have hdi_ne : d i ≠ 0 := Nat.ne_of_gt hdi
  let m : Fin 4 →₀ ℕ := d - Finsupp.single i 1
  have hmadd : m + Finsupp.single i 1 = d := by
    dsimp [m]
    exact Finsupp.sub_add_single_one_cancel hdi_ne
  have hcoeff := coeff_pderiv_backport (K := K) i F m
  rw [hderiv, hmadd] at hcoeff
  have hdcoeff : MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hcast : (((m i + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (m i)
  have hmcoeff : MvPolynomial.coeff m (MvPolynomial.C c) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero hdcoeff hcast
  have hmzero : m = 0 := by
    by_contra hm
    have h0m : (0 : Fin 4 →₀ ℕ) ≠ m := Ne.symm hm
    have hz : MvPolynomial.coeff m (MvPolynomial.C c) = 0 := by
      rw [MvPolynomial.coeff_C]
      simp [hm, h0m]
    exact hmcoeff hz
  rw [hmzero] at hmadd
  simpa using hmadd.symm

/-- Exact support normal form for a longitudinal low-dimensional face:
every supported monomial is either entirely on the `X₀` axis, or is one
pure linear transverse variable. -/
def IsLongitudinalPlanarAffineSupport
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support,
    (∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0) ∨
    ∃ i : Fin 4, i ≠ (0 : Fin 4) ∧ d = Finsupp.single i 1

/-- Exact support normal form for a base plane `(0, ell)`: every supported
monomial either lies wholly in that plane, or is one pure linear monomial in
a complementary variable. -/
def IsTransversePlanarAffineSupport
    (ell : Fin 4)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support,
    (∀ i : Fin 4,
      i ≠ (0 : Fin 4) → i ≠ ell → d i = 0) ∨
    ∃ i : Fin 4,
      i ≠ (0 : Fin 4) ∧ i ≠ ell ∧ d = Finsupp.single i 1

/-- Constant transverse gradients give the literal longitudinal
planar-affine support normal form. -/
theorem longitudinalPlanarAffineSupport_of_gradient_constant
    (F : MvPolynomial (Fin 4) K)
    (hgrad :
      ∀ i : Fin 4, i ≠ (0 : Fin 4) →
        MvPolynomial.pderiv i F =
          MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i F))) :
    IsLongitudinalPlanarAffineSupport F := by
  intro d hd
  by_cases hbase : ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0
  · exact Or.inl hbase
  · right
    push_neg at hbase
    rcases hbase with ⟨i, hi0, hdi⟩
    refine ⟨i, hi0, ?_⟩
    exact support_eq_single_of_pderiv_eq_C_of_pos
      F i (MvPolynomial.coeff 0 (MvPolynomial.pderiv i F))
      (hgrad i hi0) hd (Nat.pos_of_ne_zero hdi)

/-- Constant complementary gradients give the literal base-plane
planar-affine support normal form. -/
theorem transversePlanarAffineSupport_of_gradient_constant
    (ell : Fin 4)
    (F : MvPolynomial (Fin 4) K)
    (hgrad :
      ∀ i : Fin 4,
        i ≠ (0 : Fin 4) → i ≠ ell →
          MvPolynomial.pderiv i F =
            MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i F))) :
    IsTransversePlanarAffineSupport ell F := by
  intro d hd
  by_cases hbase :
      ∀ i : Fin 4, i ≠ (0 : Fin 4) → i ≠ ell → d i = 0
  · exact Or.inl hbase
  · right
    push_neg at hbase
    rcases hbase with ⟨i, hi0, hiell, hdi⟩
    refine ⟨i, hi0, hiell, ?_⟩
    exact support_eq_single_of_pderiv_eq_C_of_pos
      F i (MvPolynomial.coeff 0 (MvPolynomial.pderiv i F))
      (hgrad i hi0 hiell) hd (Nat.pos_of_ne_zero hdi)

/-- The low-dimensional wall face with its literal planar-affine support
normal form attached. -/
inductive DirectClosingCanonicalSquarePlanarAffineWallFaceData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop

  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (m : ℕ)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm pureLongitudinalTransverseWeight
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (hessian_support :
        ∀ i j : Fin 4,
          i ≠ (0 : Fin 4) ∨ j ≠ (0 : Fin 4) →
            HC4.Polynomial.hessian face i j = 0)
      (transverse_gradient_constant :
        ∀ i : Fin 4, i ≠ (0 : Fin 4) →
          MvPolynomial.pderiv i face =
            MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i face)))
      (support_shape : IsLongitudinalPlanarAffineSupport face)

  | transverse
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (m : ℕ)
      (hm_le : m ≤ 1)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm
          (directClosingTransverseComplementWeight D.index)
          (-(m : ℤ)) (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (hessian_support :
        ∀ i j : Fin 4,
          (i ≠ (0 : Fin 4) ∧ i ≠ D.index) ∨
          (j ≠ (0 : Fin 4) ∧ j ≠ D.index) →
            HC4.Polynomial.hessian face i j = 0)
      (base_det_zero :
        binaryDirectionalHessianDet (0 : Fin 4) D.index face = 0)
      (complement_gradient_constant :
        ∀ i : Fin 4,
          i ≠ (0 : Fin 4) → i ≠ D.index →
            MvPolynomial.pderiv i face =
              MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i face)))
      (support_shape : IsTransversePlanarAffineSupport D.index face)

/-- Promote the derivative-level low-dimensional normal form to the literal
planar-affine support normal form. -/
theorem DirectClosingCanonicalSquareLowDimensionalGradientData.toPlanarAffineData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquareLowDimensionalGradientData C heq) :
    DirectClosingCanonicalSquarePlanarAffineWallFaceData C heq := by
  cases L with
  | longitudinal D m hm_le face face_eq face_ne_zero hessian_support hgrad =>
      exact .longitudinal D m hm_le face face_eq face_ne_zero hessian_support
        hgrad (longitudinalPlanarAffineSupport_of_gradient_constant face hgrad)
  | transverse D hindex m hm_le face face_eq face_ne_zero hessian_support base_det_zero hgrad =>
      exact .transverse D hindex m hm_le face face_eq face_ne_zero hessian_support
        base_det_zero hgrad
        (transversePlanarAffineSupport_of_gradient_constant D.index face hgrad)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Strengthen the converged stationary packet -/

/-- Same converged stationary packet as before, but the canonical-wall
constructor now carries a literal planar-affine support normal form. -/
inductive AdaptiveAlignedSmithCanonicalPlanarAffineStationaryPacket
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

  | canonicalWallPlanarAffine
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
      (clock_eq :
        S.blocker.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (clock_pos : 0 < S.blocker.aligned.endpoint.defect)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (L : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquarePlanarAffineWallFaceData
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

/-- Upgrade the converged stationary packet to the literal planar-affine
normal form on its canonical-wall constructor. -/
theorem AdaptiveAlignedSmithCanonicalLowDimensionalStationaryPacket.toPlanarAffinePacket
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalLowDimensionalStationaryPacket s) :
    AdaptiveAlignedSmithCanonicalPlanarAffineStationaryPacket s := by
  cases P with
  | earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R
  | canonicalWallLowDimensional S clock_eq clock_pos C heq L =>
      exact .canonicalWallPlanarAffine S clock_eq clock_pos C heq L.toPlanarAffineData
  | zeroSchur S clock_eq clock_pos C =>
      exact .zeroSchur S clock_eq clock_pos C
  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .planarRigid S clock_eq clock_pos hall P hrigid
  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .wSquareRigid S clock_eq clock_pos hall P hrigid

/-- Final convergence frontier with the equality-wall stationary constructor
in literal planar-affine support normal form. -/
inductive AdaptiveAlignedSmithCanonicalPlanarAffineConvergenceOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | stationary
      (P : AdaptiveAlignedSmithCanonicalPlanarAffineStationaryPacket s)

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

/-- Strengthen the already-green stationary convergence result without
introducing any new branch. -/
theorem AdaptiveAlignedSmithCanonicalStationaryConvergenceOutcome.toPlanarAffineOutcome
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {RR : RepairRanking}
    {complexity : ℕ}
    (O : AdaptiveAlignedSmithCanonicalStationaryConvergenceOutcome RR s complexity) :
    AdaptiveAlignedSmithCanonicalPlanarAffineConvergenceOutcome RR s complexity := by
  cases O with
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | stationary P =>
      exact .stationary P.toPlanarAffinePacket
  | sectionGauge S clock_eq clock_pos C heq G =>
      exact .sectionGauge S clock_eq clock_pos C heq G
  | survivingExactClock W clock_eq =>
      exact .survivingExactClock W clock_eq
  | sectionBoundaryInternal B =>
      exact .sectionBoundaryInternal B

end

end HC4.Valuation
