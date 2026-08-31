import HC4.Polynomial.RankThreeDegreeOnePencilRealisation
import HC4.Polynomial.RankThreeEndpointActiveMinor
import Mathlib.Tactic

/-!
# A19.R9: endpoint active minors from the honest Euler-scaled Hessian

A19.118 proves nonvanishing for a principal `2 x 2` minor of the coefficient-
weighted endpoint pencil of the actual degree-one rank-three ray.  The Schur
calculation, however, must start from the Hessian of an honest source
polynomial.

This file closes that representation gap.  For any polynomial supported on a
literal rank-three segment of length one, the corresponding principal minor of
its Euler-scaled Hessian specialises exactly to the endpoint-pencil active
minor.  The Euler-scaled minor is just the ordinary Hessian principal minor
multiplied by `X_i^2 X_j^2`, so the nonzero endpoint pivot finally gives a
nonzero ordinary Hessian pivot on the honest ray itself.

No injectivity of the specialisation is needed for the first nonvanishing
step: a ring homomorphism sends zero to zero.
-/

namespace HC4.Polynomial

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Principal `2 x 2` minor of the ordinary polynomial Hessian. -/
def hessianPrincipalMinor
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4) : MvPolynomial (Fin 4) K :=
  hessian F i i * hessian F j j - hessian F i j * hessian F j i

/-- Principal `2 x 2` minor of the Euler-scaled Hessian of an honest
four-variable polynomial. -/
def eulerScaledHessianPrincipalMinor
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4) : MvPolynomial (Fin 4) K :=
  eulerScaledHessian F i i * eulerScaledHessian F j j -
    eulerScaledHessian F i j * eulerScaledHessian F j i

/-- Euler scaling contributes only the harmless monomial row/column factor to
a principal Hessian minor. -/
theorem eulerScaledHessianPrincipalMinor_eq_monomial_mul
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4) :
    eulerScaledHessianPrincipalMinor F i j =
      (MvPolynomial.X i) ^ 2 * (MvPolynomial.X j) ^ 2 *
        hessianPrincipalMinor F i j := by
  unfold eulerScaledHessianPrincipalMinor hessianPrincipalMinor
  rw [eulerScaledHessian_apply, eulerScaledHessian_apply,
    eulerScaledHessian_apply, eulerScaledHessian_apply]
  simp only [hessian_apply]
  ring

/-- Hence a nonzero Euler-scaled principal minor forces the corresponding
ordinary Hessian principal minor to be nonzero. -/
theorem hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4)
    (hEuler : eulerScaledHessianPrincipalMinor F i j ≠ 0) :
    hessianPrincipalMinor F i j ≠ 0 := by
  intro hzero
  apply hEuler
  rw [eulerScaledHessianPrincipalMinor_eq_monomial_mul, hzero]
  simp

/-- On an actual degree-one rank-three support line, specialisation of the
Euler-scaled principal minor is literally the coefficient-weighted endpoint
pencil minor. -/
theorem rankThree_degreeOne_specialisation_eulerScaledHessianPrincipalMinor
    {v2 v3 v4 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 u2 u3 u4 1 F)
    (i j : Fin 4) :
    let phi := rankThreeLineCoefficientPolynomial
      v2 v3 v4 1 u2 u3 u4 1 F
    rankThreeLineSpecialisation
        (eulerScaledHessianPrincipalMinor F i j) =
      weightedRankThreeEndpointActiveMinor
        (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) (u3 : K) (u4 : K)
        (phi.coeff 0) (phi.coeff 1) i j := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 1 u2 u3 u4 1 F
  have hdeg : phi.natDegree ≤ 1 := by
    dsimp [phi]
    exact rankThreeLineCoefficientPolynomial_natDegree_le
      v2 v3 v4 1 u2 u3 u4 1 F
  have hF :
      F = rankThreeLinePolynomial
        v2 v3 v4 1 u2 u3 u4 1 phi := by
    dsimp [phi]
    exact eq_rankThreeLinePolynomial_of_supported (by decide) hsupp
  have hm := rankThreeLineSpecialisation_eulerScaledHessian
    (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
    (u1 := 1) (u2 := u2) (u3 := u3) (u4 := u4)
    (M := 1) (phi := phi) hdeg
  have hphi := eq_C_add_C_mul_X_of_natDegree_le_one phi hdeg
  rw [hphi, rankThreePolynomialMomentHessian_one_linear_eq_endpointPencil] at hm
  have hentry (a b : Fin 4) :
      rankThreeLineSpecialisation
          (eulerScaledHessian F a b) =
        weightedRankThreeEndpointPencil
          (v2 : K) (v3 : K) (v4 : K)
          (1 : K) (u2 : K) (u3 : K) (u4 : K)
          (phi.coeff 0) (phi.coeff 1) a b := by
    rw [hF]
    have hab := congrFun (congrFun hm a) b
    simpa [hphi] using hab
  unfold eulerScaledHessianPrincipalMinor
    weightedRankThreeEndpointActiveMinor
  simp only [map_sub, map_mul]
  rw [hentry i i, hentry j j, hentry i j, hentry j i]

/-- For transverse source coordinates the Euler row/column monomials
specialise to one.  Hence the ordinary Hessian principal minor itself has
exactly the same endpoint-pencil specialisation. -/
theorem rankThree_degreeOne_specialisation_hessianPrincipalMinor_of_transverse
    {v2 v3 v4 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 u2 u3 u4 1 F)
    (i j : Fin 4)
    (hi : i ≠ (0 : Fin 4))
    (hj : j ≠ (0 : Fin 4)) :
    let phi := rankThreeLineCoefficientPolynomial
      v2 v3 v4 1 u2 u3 u4 1 F
    rankThreeLineSpecialisation
        (hessianPrincipalMinor F i j) =
      weightedRankThreeEndpointActiveMinor
        (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) (u3 : K) (u4 : K)
        (phi.coeff 0) (phi.coeff 1) i j := by
  dsimp only
  have h := rankThree_degreeOne_specialisation_eulerScaledHessianPrincipalMinor
    (K := K) hsupp i j
  dsimp only at h
  rw [eulerScaledHessianPrincipalMinor_eq_monomial_mul] at h
  have hXi : rankThreeLineSpecialisation (MvPolynomial.X i) = 1 := by
    fin_cases i
    · exact (hi rfl).elim
    · simp [rankThreeLineSpecialisation]
    · simp [rankThreeLineSpecialisation]
    · simp [rankThreeLineSpecialisation]
  have hXj : rankThreeLineSpecialisation (MvPolynomial.X j) = 1 := by
    fin_cases j
    · exact (hj rfl).elim
    · simp [rankThreeLineSpecialisation]
    · simp [rankThreeLineSpecialisation]
    · simp [rankThreeLineSpecialisation]
  simpa [map_mul, map_pow, hXi, hXj] using h

/-- Nonvanishing of the endpoint-pencil active minor lifts to nonvanishing of
the honest Euler-scaled Hessian principal minor. -/
theorem eulerScaledHessianPrincipalMinor_ne_zero_of_endpointActiveMinor_ne_zero
    {v2 v3 v4 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 u2 u3 u4 1 F)
    (i j : Fin 4)
    (hminor :
      let phi := rankThreeLineCoefficientPolynomial
        v2 v3 v4 1 u2 u3 u4 1 F
      weightedRankThreeEndpointActiveMinor
        (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) (u3 : K) (u4 : K)
        (phi.coeff 0) (phi.coeff 1) i j ≠ 0) :
    eulerScaledHessianPrincipalMinor F i j ≠ 0 := by
  intro hz
  have himage := congrArg (rankThreeLineSpecialisation (K := K)) hz
  rw [rankThree_degreeOne_specialisation_eulerScaledHessianPrincipalMinor
    (K := K) hsupp i j] at himage
  exact hminor (by simpa using himage)

/-- Direct endpoint-pivot to ordinary-Hessian-pivot adapter. -/
theorem hessianPrincipalMinor_ne_zero_of_endpointActiveMinor_ne_zero
    {v2 v3 v4 u2 u3 u4 : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 1 u2 u3 u4 1 F)
    (i j : Fin 4)
    (hminor :
      let phi := rankThreeLineCoefficientPolynomial
        v2 v3 v4 1 u2 u3 u4 1 F
      weightedRankThreeEndpointActiveMinor
        (v2 : K) (v3 : K) (v4 : K)
        (1 : K) (u2 : K) (u3 : K) (u4 : K)
        (phi.coeff 0) (phi.coeff 1) i j ≠ 0) :
    hessianPrincipalMinor F i j ≠ 0 :=
  hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero F i j
    (eulerScaledHessianPrincipalMinor_ne_zero_of_endpointActiveMinor_ne_zero
      hsupp i j hminor)

end

end HC4.Polynomial
