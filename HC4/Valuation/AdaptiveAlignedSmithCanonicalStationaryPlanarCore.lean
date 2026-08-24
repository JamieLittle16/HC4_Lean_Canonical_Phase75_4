import HC4.Valuation.AdaptiveAlignedSmithCanonicalLowDimensionalPlanarAffineNormalForm
import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# Separate the genuine stationary planar core from affine wall noise

A surviving canonical-square wall face has complementary degree `m ≤ 1` and
literal planar-affine support.  This leaves only two possibilities.

* `m = 0`: every supported monomial lies on the surviving one- or two-
  dimensional base.  This is the genuine nonlinear stationary core.
* `m = 1`: no base monomial can occur, so every supported monomial is a pure
  complementary linear coordinate.  Consequently every second derivative of
  the face vanishes: this branch is Hessian-invisible affine noise, not a
  planar Keller core.

This file records that dichotomy losslessly and strengthens the converged
stationary packet accordingly.  No terminal extraction and no JC2 hypothesis
is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- In the longitudinal wall, degree zero means the face is literally
supported on the marked `X₀` axis. -/
def IsLongitudinalBaseSupport
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support, ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0

/-- In the transverse wall, complementary degree zero means the face is
literally supported on the base plane `(0, ell)`. -/
def IsTransverseBaseSupport
    (ell : Fin 4)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support, ∀ i : Fin 4,
    i ≠ (0 : Fin 4) → i ≠ ell → d i = 0

/-- Pure affine support in the longitudinal wall: every monomial is one
transverse coordinate. -/
def IsLongitudinalPureAffineSupport
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support,
    ∃ i : Fin 4, i ≠ (0 : Fin 4) ∧ d = Finsupp.single i 1

/-- Pure affine support relative to `(0, ell)`: every monomial is one
coordinate complementary to the base plane. -/
def IsTransversePureAffineSupport
    (ell : Fin 4)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ F.support,
    ∃ i : Fin 4,
      i ≠ (0 : Fin 4) ∧ i ≠ ell ∧ d = Finsupp.single i 1

/-- A monomial supported on the surviving base plane has complementary degree
zero.  Keeping this as a lemma avoids dependent case-splitting on a projected
square axis later in the planar-core constructor proof. -/
theorem directClosingTransverseComplementDegree_eq_zero_of_baseSupport
    (ell : Fin 4) (d : Fin 4 →₀ ℕ)
    (hbase : ∀ i : Fin 4,
      i ≠ (0 : Fin 4) → i ≠ ell → d i = 0) :
    directClosingTransverseComplementDegree ell d = 0 := by
  fin_cases ell
  · simp [directClosingTransverseComplementDegree, Fin.sum_univ_four,
      hbase 1 (by decide) (by decide), hbase 2 (by decide) (by decide),
      hbase 3 (by decide) (by decide)]
  · simp [directClosingTransverseComplementDegree, Fin.sum_univ_four,
      hbase 2 (by decide) (by decide), hbase 3 (by decide) (by decide)]
  · simp [directClosingTransverseComplementDegree, Fin.sum_univ_four,
      hbase 1 (by decide) (by decide), hbase 3 (by decide) (by decide)]
  · simp [directClosingTransverseComplementDegree, Fin.sum_univ_four,
      hbase 1 (by decide) (by decide), hbase 2 (by decide) (by decide)]

/-- A pure longitudinal affine tail is independent of `X₀`. -/
theorem longitudinalPureAffine_pderiv_zero
    (F : MvPolynomial (Fin 4) K)
    (hsupp : IsLongitudinalPureAffineSupport F) :
    MvPolynomial.pderiv (0 : Fin 4) F = 0 := by
  apply pderiv_eq_zero_of_all_supported_exponents_zero
  intro d hd
  have hmem : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hd
  rcases hsupp d hmem with ⟨i, hi0, rfl⟩
  simp [hi0]

/-- A pure transverse affine tail is independent of both base variables. -/
theorem transversePureAffine_pderiv_zero
    (ell : Fin 4)
    (F : MvPolynomial (Fin 4) K)
    (hsupp : IsTransversePureAffineSupport ell F) :
    MvPolynomial.pderiv (0 : Fin 4) F = 0 ∧
      MvPolynomial.pderiv ell F = 0 := by
  constructor
  · apply pderiv_eq_zero_of_all_supported_exponents_zero
    intro d hd
    have hmem : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hd
    rcases hsupp d hmem with ⟨i, hi0, _hiell, rfl⟩
    simp [hi0]
  · apply pderiv_eq_zero_of_all_supported_exponents_zero
    intro d hd
    have hmem : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hd
    rcases hsupp d hmem with ⟨i, _hi0, hiell, rfl⟩
    simp [hiell]

/-- The `m = 1` longitudinal face is completely Hessian-invisible. -/
theorem longitudinalPureAffine_hessian_zero
    (F : MvPolynomial (Fin 4) K)
    (hsupp : IsLongitudinalPureAffineSupport F)
    (hgrad :
      ∀ i : Fin 4, i ≠ (0 : Fin 4) →
        MvPolynomial.pderiv i F =
          MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i F))) :
    ∀ i j : Fin 4, HC4.Polynomial.hessian F i j = 0 := by
  intro i j
  by_cases hi0 : i = (0 : Fin 4)
  · subst i
    rw [HC4.Polynomial.hessian_apply,
      longitudinalPureAffine_pderiv_zero F hsupp]
    simp
  · rw [HC4.Polynomial.hessian_apply, hgrad i hi0]
    simp

/-- The `m = 1` transverse face is completely Hessian-invisible. -/
theorem transversePureAffine_hessian_zero
    (ell : Fin 4)
    (F : MvPolynomial (Fin 4) K)
    (hsupp : IsTransversePureAffineSupport ell F)
    (hgrad :
      ∀ i : Fin 4,
        i ≠ (0 : Fin 4) → i ≠ ell →
          MvPolynomial.pderiv i F =
            MvPolynomial.C (MvPolynomial.coeff 0 (MvPolynomial.pderiv i F))) :
    ∀ i j : Fin 4, HC4.Polynomial.hessian F i j = 0 := by
  rcases transversePureAffine_pderiv_zero ell F hsupp with ⟨hzero0, hzeroell⟩
  intro i j
  by_cases hi0 : i = (0 : Fin 4)
  · subst i
    rw [HC4.Polynomial.hessian_apply, hzero0]
    simp
  · by_cases hiell : i = ell
    · subst i
      rw [HC4.Polynomial.hessian_apply, hzeroell]
      simp
    · rw [HC4.Polynomial.hessian_apply, hgrad i hi0 hiell]
      simp

/-- Exact nonlinear/affine split of a surviving planar-affine wall face. -/
inductive DirectClosingCanonicalSquareStationaryPlanarCoreData
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

  | longitudinalAffineTail
      (D : DirectClosingAlignedSquareSourceData C)
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm pureLongitudinalTransverseWeight (-1)
          (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (pure_affine : IsLongitudinalPureAffineSupport face)
      (hessian_zero :
        ∀ i j : Fin 4, HC4.Polynomial.hessian face i j = 0)

  | transverseAffineTail
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (face : MvPolynomial (Fin 4) K)
      (face_eq :
        face = Polynomial.initialForm
          (directClosingTransverseComplementWeight D.index) (-1)
          (polynomialFamilySpecialFiber D.family))
      (face_ne_zero : face ≠ 0)
      (pure_affine : IsTransversePureAffineSupport D.index face)
      (hessian_zero :
        ∀ i j : Fin 4, HC4.Polynomial.hessian face i j = 0)

/-- The planar-affine wall packet contains either a genuine degree-zero base
core or a completely Hessian-invisible degree-one affine tail. -/
theorem DirectClosingCanonicalSquarePlanarAffineWallFaceData.toStationaryPlanarCore
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (L : DirectClosingCanonicalSquarePlanarAffineWallFaceData C heq) :
    DirectClosingCanonicalSquareStationaryPlanarCoreData C heq := by
  cases L with
  | longitudinal D m hm_le face face_eq face_ne_zero hessian_support hgrad support_shape =>
      have hm_cases : m = 0 ∨ m = 1 := by omega
      rcases hm_cases with rfl | rfl
      · refine .longitudinalCore D face ?_ face_ne_zero ?_
        · simpa using face_eq
        · intro d hd i hi0
          rcases support_shape d hd with hbase | ⟨k, hk0, hk⟩
          · exact hbase i hi0
          · subst d
            have hdeg := support_initialForm_pureLongitudinalTransverseDegree_eq
              (polynomialFamilySpecialFiber D.family) 0 (by simpa [face_eq] using hd)
            fin_cases k <;> simp [directClosingLongitudinalTransverseDegree,
              Fin.sum_univ_four] at hk0 hdeg ⊢
      · have hpure : IsLongitudinalPureAffineSupport face := by
          intro d hd
          rcases support_shape d hd with hbase | hpure
          · have hdeg := support_initialForm_pureLongitudinalTransverseDegree_eq
              (polynomialFamilySpecialFiber D.family) 1 (by simpa [face_eq] using hd)
            have hz : directClosingLongitudinalTransverseDegree d = 0 := by
              simp [directClosingLongitudinalTransverseDegree, Fin.sum_univ_four,
                hbase 1 (by decide), hbase 2 (by decide), hbase 3 (by decide)]
            omega
          · exact hpure
        refine .longitudinalAffineTail D face ?_ face_ne_zero hpure ?_
        · simpa using face_eq
        · exact longitudinalPureAffine_hessian_zero face hpure hgrad

  | transverse D hindex m hm_le face face_eq face_ne_zero hessian_support base_det_zero hgrad support_shape =>
      have hm_cases : m = 0 ∨ m = 1 := by omega
      rcases hm_cases with rfl | rfl
      · refine .transverseCore D hindex face ?_ face_ne_zero ?_ base_det_zero
        · simpa using face_eq
        · intro d hd i hi0 hiell
          rcases support_shape d hd with hbase | ⟨k, hk0, hkell, hk⟩
          · exact hbase i hi0 hiell
          · subst d
            have hdeg := support_initialForm_transverseComplementDegree_eq
              D.index (polynomialFamilySpecialFiber D.family) 0
              (by simpa [face_eq] using hd)
            have hone :
                directClosingTransverseComplementDegree D.index
                    (Finsupp.single k 1) = 1 := by
              have hadd := directClosingTransverseComplementDegree_add_single
                D.index k hk0 hkell (0 : Fin 4 →₀ ℕ)
              have hzero :
                  directClosingTransverseComplementDegree D.index
                      (0 : Fin 4 →₀ ℕ) = 0 := by
                exact directClosingTransverseComplementDegree_eq_zero_of_baseSupport
                  D.index 0 (by intro i hi0 hiell; simp)
              simpa only [zero_add, hzero] using hadd
            omega
      · have hpure : IsTransversePureAffineSupport D.index face := by
          intro d hd
          rcases support_shape d hd with hbase | hpure
          · have hdeg := support_initialForm_transverseComplementDegree_eq
              D.index (polynomialFamilySpecialFiber D.family) 1
              (by simpa [face_eq] using hd)
            have hz : directClosingTransverseComplementDegree D.index d = 0 := by
              exact directClosingTransverseComplementDegree_eq_zero_of_baseSupport
                D.index d hbase
            omega
          · exact hpure
        refine .transverseAffineTail D hindex face ?_ face_ne_zero hpure ?_
        · simpa using face_eq
        · exact transversePureAffine_hessian_zero D.index face hpure hgrad

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Strengthen the common stationary packet by splitting wall noise -/

/-- The common stationary packet with its canonical-wall branch separated
into a genuine planar core versus a Hessian-invisible affine tail. -/
inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCorePacket
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
      (L : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareStationaryPlanarCoreData
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

/-- Upgrade the already-converged packet by performing the exact `m = 0/1`
wall split. -/
theorem AdaptiveAlignedSmithCanonicalPlanarAffineStationaryPacket.toStationaryPlanarCorePacket
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalPlanarAffineStationaryPacket s) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCorePacket s := by
  cases P with
  | earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R =>
      exact .earlySchurConstantRS2 S clock_eq clock_pos C hlt htangential R
  | canonicalWallPlanarAffine S clock_eq clock_pos C heq L =>
      exact .canonicalWall S clock_eq clock_pos C heq L.toStationaryPlanarCore
  | zeroSchur S clock_eq clock_pos C =>
      exact .zeroSchur S clock_eq clock_pos C
  | planarRigid S clock_eq clock_pos hall P hrigid =>
      exact .planarRigid S clock_eq clock_pos hall P hrigid
  | wSquareRigid S clock_eq clock_pos hall P hrigid =>
      exact .wSquareRigid S clock_eq clock_pos hall P hrigid

end

end HC4.Valuation
