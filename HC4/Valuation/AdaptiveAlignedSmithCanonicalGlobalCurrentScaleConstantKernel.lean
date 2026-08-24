import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBlockerRationalNormalization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidElimination
import Mathlib.Tactic

/-!
# A18.4.34: spend the literal right-recentered kernel at the current scale

The A17 rigid/closing algebra is already source-honest: it ends in a literal
constant Hessian-kernel vector of the actual right-recentered special fibre.
Its historical final adapter, however, packages the preceding aligned Smith
move as a fresh factor `20`.  A boundary-produced presented blocker is already
past that move, so reusing the old adapter would count the Smith
ramification twice.

This file changes only that final bookkeeping layer.  Starting from a
stationary blocker whose endpoint clock is literally the current state's raw
clock, we perform the same determinant-one source transvections and source
sign change as A17.3E, record them as a factor-one internal presentation at
the existing absolute scale, and invoke the already-green generic
scale-aware kernel-free spend.

Consequently the deep A17 rigid proof can be reused unchanged: its final
`AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData` now spends
from the actual presented state.  No new geometry or homogeneity hypothesis is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem currentScale_mvC_mul_mvC_div_cancel
    (x y : K) (hy : y ≠ 0) :
    (MvPolynomial.C y : MvPolynomial (Fin 4) K) * MvPolynomial.C (x / y) =
      MvPolynomial.C x := by
  rw [← MvPolynomial.C_mul]
  have hscalar : y * (x / y) = x := by
    field_simp [hy]
  rw [hscalar]

/-- Current-scale version of A17.3E's three-shear helper.  The transformed
right-recentered family has the same raw Hessian clock and is recorded at the
same absolute scale as `s`; only the later kernel first-contact contributes a
positive ramification factor. -/
theorem exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero_currentScale
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (ell k₁ k₂ k₃ : Fin 4)
    (hell0 : ell ≠ (0 : Fin 4))
    (hk₁ : k₁ ≠ ell) (hk₂ : k₂ ≠ ell) (hk₃ : k₃ ≠ ell)
    (a₁ a₂ a₃ : K)
    (hpderiv :
      MvPolynomial.pderiv ell
        (tripleTransverseSourceShearFamilyBase
          k₁ k₂ k₃ ell a₁ a₂ a₃
          (polynomialFamilySpecialFiber
            S.blocker.aligned.endpoint.rightRecenteredFamily)) = 0) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  let E := S.blocker.aligned.endpoint
  let Pshear := tripleTransverseSourceShearFamily
    k₁ k₂ k₃ ell a₁ a₂ a₃ E.rightRecenteredFamily
  let bshear := tripleTransverseSourceUnshearSection
    k₁ k₂ k₃ ell a₁ a₂ a₃ E.rightRecenteredRightSection
  let Psign := allSourceSignHom (R := Polynomial K) Pshear
  let bsign := polynomialSectionNegation (K := K) bshear

  have hdefShear :
      HasPolynomialFamilyHessianDefect (K := K) Pshear E.defect := by
    dsimp [Pshear]
    exact tripleTransverseSourceShearFamily_preservesHessianDefect
      k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
      E.rightRecenteredFamily E.rightRecenteredFamily_hessianDefect
  have hdefSign :
      HasPolynomialFamilyHessianDefect (K := K) Psign E.defect := by
    dsimp [Psign]
    exact allSourceSignHom_preservesHessianDefect Pshear hdefShear

  have hdegree0 : NonlinearDegreeBound s.degreeCap E.rightRecenteredFamily := by
    exact E.rightRecenteredFamily_nonlinearDegreeBound
  have hdegree1 :
      NonlinearDegreeBound s.degreeCap
        (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁)
          E.rightRecenteredFamily) :=
    nonlinearDegreeBound_transverseSourceShear
      s.degreeCap k₁ ell (Polynomial.C a₁) E.rightRecenteredFamily hdegree0
  have hdegree2 :
      NonlinearDegreeBound s.degreeCap
        (transverseSourceShearHom (K := K) k₂ ell (Polynomial.C a₂)
          (transverseSourceShearHom (K := K) k₁ ell (Polynomial.C a₁)
            E.rightRecenteredFamily)) :=
    nonlinearDegreeBound_transverseSourceShear
      s.degreeCap k₂ ell (Polynomial.C a₂) _ hdegree1
  have hdegreeShear : NonlinearDegreeBound s.degreeCap Pshear := by
    dsimp [Pshear, tripleTransverseSourceShearFamily]
    exact nonlinearDegreeBound_transverseSourceShear
      s.degreeCap k₃ ell (Polynomial.C a₃) _ hdegree2
  have hdegreeSign : NonlinearDegreeBound s.degreeCap Psign := by
    dsimp [Psign]
    exact nonlinearDegreeBound_allSourceSignHom s.degreeCap Pshear hdegreeShear

  have hcollShear :
      HasPolynomialFamilyExactGradientCollision
        Pshear (zeroPolynomialSection (K := K)) bshear := by
    dsimp [Pshear, bshear]
    exact polynomialFamilyExactGradientCollision_tripleTransverseSourceShear
      k₁ k₂ k₃ ell hk₁ hk₂ hk₃ a₁ a₂ a₃
      E.rightRecenteredFamily E.rightRecenteredRightSection
        E.rightRecenteredFamily_exactCollision
  have hcollSignRaw :=
    polynomialFamilyExactGradientCollision_allSourceSign
      (K := K) Pshear (zeroPolynomialSection (K := K)) bshear hcollShear
  have hcollSign :
      HasPolynomialFamilyExactGradientCollision
        Psign (zeroPolynomialSection (K := K)) bsign := by
    simpa [Psign, bsign] using hcollSignRaw

  have hspecialShear :
      polynomialSectionSpecialPoint bshear =
        (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
    dsimp [bshear]
    exact polynomialSectionSpecialPoint_tripleTransverseUnshear_negAxis
      k₁ k₂ k₃ ell hell0 a₁ a₂ a₃ E.rightRecenteredRightSection
      E.rightRecenteredRightSection_specialPoint
  have hspecialSign :
      polynomialSectionSpecialPoint bsign =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    have hi := congrFun hspecialShear i
    change Polynomial.constantCoeff (bshear i) =
      - coordinateAxisPoint (K := K) (0 : Fin 4) i at hi
    change Polynomial.constantCoeff (-bshear i) =
      coordinateAxisPoint (K := K) (0 : Fin 4) i
    rw [map_neg, hi]
    simp

  have hspecialFiberShear :
      polynomialFamilySpecialFiber Pshear =
        tripleTransverseSourceShearFamilyBase
          k₁ k₂ k₃ ell a₁ a₂ a₃
          (polynomialFamilySpecialFiber E.rightRecenteredFamily) := by
    dsimp [Pshear]
    exact polynomialFamilySpecialFiber_tripleTransverseSourceShearFamily
      k₁ k₂ k₃ ell a₁ a₂ a₃ E.rightRecenteredFamily
  have hpderivSign :
      MvPolynomial.pderiv ell (polynomialFamilySpecialFiber Psign) = 0 := by
    dsimp [Psign]
    rw [polynomialFamilySpecialFiber_allSourceSignHom]
    rw [pderiv_allSourceSignHom]
    rw [hspecialFiberShear, hpderiv]
    simp
  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber Psign).support,
        d ell = 0 := by
    intro d hd
    exact exponent_eq_zero_of_pderiv_eq_zero
      ell (polynomialFamilySpecialFiber Psign) hpderivSign d
      (MvPolynomial.mem_support_iff.mp hd)

  let outer : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { rawDefect := E.defect
      scale := s.scale
      scale_pos := s.scale_pos
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := Psign
      movingSection := bsign
      hessianDefect := hdefSign
      nonlinearDegreeBound := hdegreeSign
      exactCollision := hcollSign
      sectionSpecial := hspecialSign }

  have hmove : HasCertifiedRamifiedEpisodeInternalMove outer s := by
    change Nonempty (CertifiedRamifiedEpisodeInternalMove outer s)
    exact ⟨{
      ramification := 1
      ramification_pos := by omega
      scale_eq := by simp [outer]
      raw_eq := by simpa [outer, E] using clock_eq
      degreeCap_eq := rfl
      sourceComplexity_eq := rfl
      repair_eq := rfl
    }⟩

  rcases outer.exists_certifiedRamifiedRawDefectSpend_of_specialFiber_free
      ell hell0 (by simpa [outer] using hfree) with ⟨target, hspend⟩
  exact ⟨target, hmove.then_spend hspend⟩

namespace AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

/-- A literal transverse constant kernel on an already-presented stationary
blocker spends from that current state, not from a fictitious pre-aligned
state. -/
theorem exists_ramifiedSpend_currentScale
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (D : AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData S) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rcases D.transverse with ⟨ell, hell0, hvell⟩
  let F := polynomialFamilySpecialFiber S.blocker.aligned.endpoint.rightRecenteredFamily
  have hdir := D.directionalDerivative_eq_zero
  change constantSourceDirectionalDerivative F D.direction = 0 at hdir

  fin_cases ell
  · exact False.elim (hell0 rfl)
  · let combo :=
      MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 1) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 2 / D.direction 1) *
          MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.direction 3 / D.direction 1) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.direction (1 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 1) =
            MvPolynomial.C (D.direction 0) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 1) =
            MvPolynomial.C (D.direction 2) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 1) =
            MvPolynomial.C (D.direction 3) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (1 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (1 : Fin 4)) *
                (MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 1) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 2 / D.direction 1) *
                    MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.direction 3 / D.direction 1) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 0 / D.direction 1)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 2 / D.direction 1)) *
                  MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.direction 1) *
                    MvPolynomial.C (D.direction 3 / D.direction 1)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h2C, h3C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (1 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (1 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
            (D.direction 0 / D.direction 1)
            (D.direction 2 / D.direction 1)
            (D.direction 3 / D.direction 1) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (2 : Fin 4) (3 : Fin 4) (1 : Fin 4)
          (D.direction 0 / D.direction 1)
          (D.direction 2 / D.direction 1)
          (D.direction 3 / D.direction 1)) hcombo
    exact exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero_currentScale
      S clock_eq
      (1 : Fin 4) (0 : Fin 4) (2 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 1)
      (D.direction 2 / D.direction 1)
      (D.direction 3 / D.direction 1) hp
  · let combo :=
      MvPolynomial.pderiv (2 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 2) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 1 / D.direction 2) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 3 / D.direction 2) *
          MvPolynomial.pderiv (3 : Fin 4) F
    have hv : D.direction (2 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 2) =
            MvPolynomial.C (D.direction 0) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 2) =
            MvPolynomial.C (D.direction 1) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 2) =
            MvPolynomial.C (D.direction 3) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (2 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (2 : Fin 4)) *
                (MvPolynomial.pderiv (2 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 2) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 1 / D.direction 2) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 3 / D.direction 2) *
                    MvPolynomial.pderiv (3 : Fin 4) F) =
              MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 0 / D.direction 2)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 1 / D.direction 2)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 2) *
                    MvPolynomial.C (D.direction 3 / D.direction 2)) *
                  MvPolynomial.pderiv 3 F := by ring
          _ = MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F := by
              rw [h0C, h1C, h3C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (2 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (2 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
            (D.direction 0 / D.direction 2)
            (D.direction 1 / D.direction 2)
            (D.direction 3 / D.direction 2) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (3 : Fin 4) (2 : Fin 4)
          (D.direction 0 / D.direction 2)
          (D.direction 1 / D.direction 2)
          (D.direction 3 / D.direction 2)) hcombo
    exact exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero_currentScale
      S clock_eq
      (2 : Fin 4) (0 : Fin 4) (1 : Fin 4) (3 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 2)
      (D.direction 1 / D.direction 2)
      (D.direction 3 / D.direction 2) hp
  · let combo :=
      MvPolynomial.pderiv (3 : Fin 4) F +
        MvPolynomial.C (D.direction 0 / D.direction 3) *
          MvPolynomial.pderiv (0 : Fin 4) F +
        MvPolynomial.C (D.direction 1 / D.direction 3) *
          MvPolynomial.pderiv (1 : Fin 4) F +
        MvPolynomial.C (D.direction 2 / D.direction 3) *
          MvPolynomial.pderiv (2 : Fin 4) F
    have hv : D.direction (3 : Fin 4) ≠ 0 := by simpa using hvell
    have hcombo : combo = 0 := by
      have h0C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 0 / D.direction 3) =
            MvPolynomial.C (D.direction 0) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 3) =
            MvPolynomial.C (D.direction 1) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 3) =
            MvPolynomial.C (D.direction 2) :=
        currentScale_mvC_mul_mvC_div_cancel _ _ hv
      have hscaled :
          MvPolynomial.C (D.direction (3 : Fin 4)) * combo =
            constantSourceDirectionalDerivative F D.direction := by
        dsimp [combo]
        calc
          MvPolynomial.C (D.direction (3 : Fin 4)) *
                (MvPolynomial.pderiv (3 : Fin 4) F +
                  MvPolynomial.C (D.direction 0 / D.direction 3) *
                    MvPolynomial.pderiv (0 : Fin 4) F +
                  MvPolynomial.C (D.direction 1 / D.direction 3) *
                    MvPolynomial.pderiv (1 : Fin 4) F +
                  MvPolynomial.C (D.direction 2 / D.direction 3) *
                    MvPolynomial.pderiv (2 : Fin 4) F) =
              MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 0 / D.direction 3)) *
                  MvPolynomial.pderiv 0 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 1 / D.direction 3)) *
                  MvPolynomial.pderiv 1 F +
                (MvPolynomial.C (D.direction 3) *
                    MvPolynomial.C (D.direction 2 / D.direction 3)) *
                  MvPolynomial.pderiv 2 F := by ring
          _ = MvPolynomial.C (D.direction 3) * MvPolynomial.pderiv 3 F +
                MvPolynomial.C (D.direction 0) * MvPolynomial.pderiv 0 F +
                MvPolynomial.C (D.direction 1) * MvPolynomial.pderiv 1 F +
                MvPolynomial.C (D.direction 2) * MvPolynomial.pderiv 2 F := by
              rw [h0C, h1C, h2C]
          _ = constantSourceDirectionalDerivative F D.direction := by
              simp [constantSourceDirectionalDerivative, Fin.sum_univ_four]
              ring
      have hz : MvPolynomial.C (D.direction (3 : Fin 4)) * combo = 0 := by
        rw [hscaled, hdir]
      exact (mul_eq_zero.mp hz).resolve_left (by simpa using hv)
    have hp :
        MvPolynomial.pderiv (3 : Fin 4)
          (tripleTransverseSourceShearFamilyBase
            (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
            (D.direction 0 / D.direction 3)
            (D.direction 1 / D.direction 3)
            (D.direction 2 / D.direction 3) F) = 0 := by
      rw [pderiv_source_tripleTransverseSourceShearFamilyBase
        (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
        (by decide) (by decide) (by decide)]
      simpa [combo] using congrArg
        (tripleTransverseSourceShearFamilyBase
          (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (D.direction 0 / D.direction 3)
          (D.direction 1 / D.direction 3)
          (D.direction 2 / D.direction 3)) hcombo
    exact exists_ramifiedSpend_of_rightRecentered_tripleShear_pderiv_zero_currentScale
      S clock_eq
      (3 : Fin 4) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 3)
      (D.direction 1 / D.direction 3)
      (D.direction 2 / D.direction 3) hp

end AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

namespace AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData

/-- The complete A17.3F rigid algebra is scale-free until its final spend.
Use its literal constant-kernel output with the current-scale adapter above. -/
theorem exists_ramifiedSpend_currentScale
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (T : AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData S) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
  rcases T.toRightRecenteredConstantKernelData with ⟨D⟩
  exact D.exists_ramifiedSpend_currentScale S clock_eq

end AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData

end

end HC4.Valuation
