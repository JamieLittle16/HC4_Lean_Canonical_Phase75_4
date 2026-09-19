import HC4.Valuation.AdaptiveAlignedSmithCanonicalCurrentScaleCompleteFirstContact
import HC4.Valuation.AdaptiveAlignedSmithCanonicalConstantKernelFirstContact
import Mathlib.Tactic

/-!
# A18.4.71: literal transverse constant kernel is directly rank two

A18.4.48 performs the complete finite coordinate straightening of a literal
constant Hessian-kernel vector.  Its only remaining non-rank-two output came
from the old kernel-linear first-contact branch.  A18.4.69 has removed that
branch for the exact triple-shear presentations used here.

This file reruns the A18.4.48 coordinate split and changes only the final
triple-shear call.  Therefore every literal transverse constant kernel of the
honest right-recentered blocker special fibre produces actual post-opening
Hessian geometry and a geometry-backed rank-two target.  There is no
same-scale recursive alternative.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

private theorem completeRankTwo_mvC_mul_mvC_div_cancel
    (x y : K) (hy : y ≠ 0) :
    (MvPolynomial.C y : MvPolynomial (Fin 4) K) * MvPolynomial.C (x / y) =
      MvPolynomial.C x := by
  rw [← MvPolynomial.C_mul]
  have hscalar : y * (x / y) = x := by
    field_simp [hy]
  rw [hscalar]

namespace AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

/-- **Complete constant-kernel first-contact closure at the current scale.** -/
theorem completeRankTwoProgress_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (D : AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData S) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
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
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 1) =
            MvPolynomial.C (D.direction 2) :=
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (1 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 1) =
            MvPolynomial.C (D.direction 3) :=
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
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
    exact currentScaleCompleteRankTwo_of_rightRecentered_tripleShear_pderiv_zero
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
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 2) =
            MvPolynomial.C (D.direction 1) :=
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
      have h3C :
          (MvPolynomial.C (D.direction (2 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 3 / D.direction 2) =
            MvPolynomial.C (D.direction 3) :=
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
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
    exact currentScaleCompleteRankTwo_of_rightRecentered_tripleShear_pderiv_zero
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
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
      have h1C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 1 / D.direction 3) =
            MvPolynomial.C (D.direction 1) :=
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
      have h2C :
          (MvPolynomial.C (D.direction (3 : Fin 4)) : MvPolynomial (Fin 4) K) *
              MvPolynomial.C (D.direction 2 / D.direction 3) =
            MvPolynomial.C (D.direction 2) :=
        completeRankTwo_mvC_mul_mvC_div_cancel _ _ hv
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
    exact currentScaleCompleteRankTwo_of_rightRecentered_tripleShear_pderiv_zero
      RR complexity hsrepair S clock_eq
      (3 : Fin 4) (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)
      (by decide) (by decide) (by decide) (by decide)
      (D.direction 0 / D.direction 3)
      (D.direction 1 / D.direction 3)
      (D.direction 2 / D.direction 3) hp

end AdaptiveAlignedSmithCanonicalRightRecenteredConstantKernelData

namespace AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData

/-- The deep rigid mixed-layer cross chain also ends directly in complete
geometry-backed rank-two progress. -/
theorem completeRankTwoProgress_currentScale
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)
    (clock_eq : S.blocker.aligned.endpoint.defect = s.rawDefect)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (T : AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData S) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
        RR s complexity) := by
  rcases T.toRightRecenteredConstantKernelData with ⟨D⟩
  exact D.completeRankTwoProgress_currentScale
    RR S clock_eq complexity hsrepair

end AdaptiveAlignedSmithCanonicalRigidMixedLayerCrossData

end

end HC4.Valuation
