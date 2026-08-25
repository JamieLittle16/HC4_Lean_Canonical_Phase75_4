import HC4.Polynomial.RankThreeWeightedPencils
import HC4.Polynomial.RankThreeLineReconstruction
import Mathlib.Tactic

/-!
# A18.5.48: an actual degree-one supported edge is the weighted endpoint pencil

A18.5.6 already proves that zero Hessian of the honest finite rank-three line
forces the determinant of its polynomial moment matrix to vanish.  At segment
length `M=1` the extracted coefficient polynomial has degree at most one, so
it is literally

    C(phi.coeff 0) + C(phi.coeff 1) X.

A18.5.46 then identifies the moment matrix with the coefficient-weighted
endpoint pencil.  This closes the last representation gap between an actual
Newton edge and the exact terminal determinant calculations.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Any polynomial of natural degree at most one is determined by its first
two coefficients in the expected form. -/
theorem eq_C_add_C_mul_X_of_natDegree_le_one
    (p : Polynomial K) (hdeg : p.natDegree ≤ 1) :
    p = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff 1) * Polynomial.X := by
  apply Polynomial.ext
  intro n
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp
  · have hn : p.natDegree < n + 2 := by omega
    have hz : p.coeff (n + 2) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hn
    simp [hz]

/-- For `M=1`, the finite integral moment matrix is exactly the weighted
pencil of the two honest endpoint exponent vectors. -/
set_option maxHeartbeats 4000000 in
theorem rankThreePolynomialMomentHessian_one_linear_eq_endpointPencil
    (v2 v3 v4 u1 u2 u3 u4 : ℕ) (c0 c1 : K) :
    rankThreePolynomialMomentHessian
        v2 v3 v4 u1 u2 u3 u4 1
        (Polynomial.C c0 + Polynomial.C c1 * Polynomial.X) =
      weightedRankThreeEndpointPencil
        (v2 : K) (v3 : K) (v4 : K)
        (u1 : K) (u2 : K) (u3 : K) (u4 : K) c0 c1 := by
  simpa [rankThreePolynomialMomentHessian,
    rankThreeIntegralLineBaseExponent,
    rankThreeIntegralLineDirection] using
    (rankThreeAffinePolynomialMomentHessian_linear_eq_endpointPencil
      (K := K)
      (v2 : K) (v3 : K) (v4 : K)
      (u1 : K) (u2 : K) (u3 : K) (u4 : K) c0 c1)

/-- **Actual degree-one supported edge -> zero weighted endpoint pencil.** -/
theorem supported_rankThree_degreeOne_endpointPencil_det_zero
    {v2 v3 v4 u1 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hu1 : 0 < u1)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 1 F)
    (hdet : hessianDeterminant F = 0) :
    let phi := rankThreeLineCoefficientPolynomial
      v2 v3 v4 u1 u2 u3 u4 1 F
    (weightedRankThreeEndpointPencil
      (v2 : K) (v3 : K) (v4 : K)
      (u1 : K) (u2 : K) (u3 : K) (u4 : K)
      (phi.coeff 0) (phi.coeff 1)).det = 0 := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 1 F
  have hdeg : phi.natDegree ≤ 1 := by
    dsimp [phi]
    exact rankThreeLineCoefficientPolynomial_natDegree_le
      v2 v3 v4 u1 u2 u3 u4 1 F
  have hline :
      F = rankThreeLinePolynomial
        v2 v3 v4 u1 u2 u3 u4 1 phi := by
    dsimp [phi]
    exact eq_rankThreeLinePolynomial_of_supported hu1 hsupp
  have hdetLine :
      hessianDeterminant
        (rankThreeLinePolynomial
          v2 v3 v4 u1 u2 u3 u4 1 phi) = 0 := by
    rw [← hline]
    exact hdet
  have hmoment :=
    rankThreePolynomialMoment_det_zero_of_hessianDeterminant_zero
      (K := K)
      (v2 := v2) (v3 := v3) (v4 := v4)
      (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
      (M := 1) (phi := phi) hu1 hdeg hdetLine
  have hphi := eq_C_add_C_mul_X_of_natDegree_le_one phi hdeg
  rw [hphi,
    rankThreePolynomialMomentHessian_one_linear_eq_endpointPencil] at hmoment
  exact hmoment

end

end HC4.Polynomial
