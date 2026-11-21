import HC4.Valuation.AdaptiveAlignedSmithCanonicalCurrentScaleFirstContact
import Mathlib.Tactic

/-!
# A18.4.48: literal transverse constant kernel closes without rational descent

A18.4.47 supplies the sound replacement for the final triple-shear helper.
This file reruns the already-green finite coordinate straightening from
A18.4.34 and changes only its final call.

Thus a literal constant Hessian-kernel direction of the honest right-recentered
special fibre now yields either

* same-scale strict progress from the actual incoming state; or
* a geometry-backed rank-two macro on the actual saturated-opening family.

The proof below is intentionally parallel to A18.4.34 so that no new linear
algebra is hidden in the final assembly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem firstContact_mvC_mul_mvC_div_cancel
    (x y : K) (hy : y ≠ 0) :
    (MvPolynomial.C y : MvPolynomial (Fin 4) K) * MvPolynomial.C (x / y) =
      MvPolynomial.C x := by
  rw [← MvPolynomial.C_mul]
  have hscalar : y * (x / y) = x := by
    field_simp [hy]
  rw [hscalar]

namespace AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

/-- Geometry-preserving replacement for
`exists_ramifiedSpend_currentScale`. -/
theorem sameScale_or_rankTwoProgress_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (D : AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData S) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
          RR s complexity) := by
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
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 1) =
            MvPolynomial.C (D.direction 2) :=
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 1) =
            MvPolynomial.C (D.direction 3) :=
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
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
    exact currentScaleFirstContact_of_rightRecentered_tripleShear_pderiv_zero
      RR complexity hsrepair S clock_eq
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
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 2) =
            MvPolynomial.C (D.direction 1) :=
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 2) =
            MvPolynomial.C (D.direction 3) :=
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
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
    exact currentScaleFirstContact_of_rightRecentered_tripleShear_pderiv_zero
      RR complexity hsrepair S clock_eq
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
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 3) =
            MvPolynomial.C (D.direction 1) :=
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 3) =
            MvPolynomial.C (D.direction 2) :=
        firstContact_mvC_mul_mvC_div_cancel _ _ hv
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
    exact currentScaleFirstContact_of_rightRecentered_tripleShear_pderiv_zero
      RR complexity hsrepair S clock_eq
      (3 : Fin 4) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 3)
      (D.direction 1 / D.direction 3)
      (D.direction 2 / D.direction 3) hp

end AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

namespace AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData

/-- The rigid A17 algebra now ends in first-contact termination rather than a
bare ramified spend. -/
theorem sameScale_or_rankTwoProgress_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (T : AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData S) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalFactorOneKernelOpeningRankTwoProgress
          RR s complexity) := by
  rcases T.toRightRecenteredConstantKernelData with ⟨D⟩
  exact D.sameScale_or_rankTwoProgress_currentScale
    RR S clock_eq complexity hsrepair

end AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData

end

end HC4.Valuation
