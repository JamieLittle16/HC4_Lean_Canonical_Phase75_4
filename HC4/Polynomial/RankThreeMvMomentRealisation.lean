import HC4.Polynomial.RankThreeMvSubstitution
import HC4.Polynomial.RankThreeFractionMomentBridge
import HC4.Polynomial.ComplementaryMvMomentRealisation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# A18.5.6: realise the rank-three moment Hessian from an honest MvPolynomial

This is the rank-three analogue of `ComplementaryMvMomentRealisation`.
For the honest line segment introduced in A18.5.4, Euler-scaled second
source derivatives are specialised along

    x0 = X, x1 = x2 = x3 = 1.

The resulting polynomial-valued matrix is exactly the line-moment Hessian,
followed by the injective substitution `X -> X^u1`.  Consequently a zero
ordinary Hessian determinant of the honest multivariate rank-three line gives
the moment determinant equation and hence the mature
`RankThreeFractionCoreDetZero` predicate.

No Laurent polynomial and no division in the multivariate source ring is used.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- Coefficient-field value of an honest exponent on the rank-three line. -/
def rankThreeLineExponentValue
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ) : Fin 4 → K :=
  fun i =>
    ((rankThreeLineExponentFinsupp
      v2 v3 v4 u1 u2 u3 u4 M j i : ℕ) : K)

/-- The exponent value is the affine rank-three exponent on the intended
support range. -/
theorem rankThreeLineExponentValue_eq_affine
    {K : Type*} [Field K] [CharZero K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ)
    (hj : j ≤ M) :
    rankThreeLineExponentValue (K := K)
        v2 v3 v4 u1 u2 u3 u4 M j =
      fun i =>
        rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
          (j : K) *
            rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 i := by
  exact rankThreeLineExponentFinsupp_cast_eq_affine
    (K := K) v2 v3 v4 u1 u2 u3 u4 M j hj

/-- Euler differentiation of one honest rank-three line term multiplies it by
its corresponding source exponent. -/
theorem mvEuler_rankThreeLineTerm
    {K : Type*} [Field K] [CharZero K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ)
    (c : K) (i : Fin 4) :
    mvEuler i (rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c) =
      MvPolynomial.C
          (rankThreeLineExponentValue (K := K)
            v2 v3 v4 u1 u2 u3 u4 M j i) *
        rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c := by
  rw [rankThreeLineTerm_eq_monomial]
  unfold mvEuler
  rw [MvPolynomial.X_mul_pderiv_monomial]
  rw [← rankThreeLineTerm_eq_monomial]
  simp [rankThreeLineExponentValue, nsmul_eq_mul]

/-- Euler-scaled Hessian of one line term has the expected exponent-core
coefficient. -/
theorem eulerScaledHessian_rankThreeLineTerm
    {K : Type*} [Field K] [CharZero K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ)
    (c : K) (i l : Fin 4) :
    eulerScaledHessian
        (rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c) i l =
      MvPolynomial.C
          (rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j i *
            rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j l -
            if i = l then
              rankThreeLineExponentValue (K := K)
                v2 v3 v4 u1 u2 u3 u4 M j i
            else 0) *
        rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c := by
  change
    mvEuler i
          (mvEuler l
            (rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c)) -
        (if i = l then
          mvEuler i (rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c)
        else 0) = _
  rw [mvEuler_rankThreeLineTerm
    (K := K) v2 v3 v4 u1 u2 u3 u4 M j c l]
  rw [mvEuler_C_mul]
  rw [mvEuler_rankThreeLineTerm
    (K := K) v2 v3 v4 u1 u2 u3 u4 M j c i]
  by_cases hil : i = l
  · subst l
    simp [MvPolynomial.C_mul, MvPolynomial.C_sub]
    ring
  · simp [hil, MvPolynomial.C_mul]
    ring

/-- Specialised one-term Euler-Hessian formula. -/
theorem rankThreeLineSpecialisation_eulerScaledHessian_term
    {K : Type*} [Field K] [CharZero K]
    (v2 v3 v4 u1 u2 u3 u4 M j : ℕ)
    (c : K) (i l : Fin 4) :
    rankThreeLineSpecialisation
        (eulerScaledHessian
          (rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j c) i l) =
      Polynomial.C
          (rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j i *
            rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j l -
            if i = l then
              rankThreeLineExponentValue (K := K)
                v2 v3 v4 u1 u2 u3 u4 M j i
            else 0) *
        (Polynomial.C c * Polynomial.X ^ (j * u1)) := by
  rw [eulerScaledHessian_rankThreeLineTerm]
  rw [map_mul]
  rw [rankThreeLineSpecialisation_term]
  have hC :
      rankThreeLineSpecialisation
        (MvPolynomial.C
          (rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j i *
            rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j l -
            if i = l then
              rankThreeLineExponentValue (K := K)
                v2 v3 v4 u1 u2 u3 u4 M j i
            else 0)) =
        Polynomial.C
          (rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j i *
            rankThreeLineExponentValue (K := K)
              v2 v3 v4 u1 u2 u3 u4 M j l -
            if i = l then
              rankThreeLineExponentValue (K := K)
                v2 v3 v4 u1 u2 u3 u4 M j i
            else 0) := by
    simp [rankThreeLineSpecialisation]
  rw [hC]

/-- Polynomial-valued rank-three line-moment matrix. -/
def rankThreePolynomialMomentHessian
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  lineMomentHessian
    (fun i => Polynomial.C
      (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i))
    (fun i => Polynomial.C
      (rankThreeIntegralLineDirection (K := K)
        v2 v3 v4 u1 u2 u3 u4 i))
    phi (eulerDerivative phi) (eulerDerivative (eulerDerivative phi))

/-- Entrywise normal form of the polynomial-valued rank-three moment Hessian. -/
theorem rankThreePolynomialMomentHessian_apply
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) (i l : Fin 4) :
    rankThreePolynomialMomentHessian
        v2 v3 v4 u1 u2 u3 u4 M phi i l =
      phi * Polynomial.C
        (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i *
            rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M l -
          if i = l then
            rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i
          else 0) +
      eulerDerivative phi * Polynomial.C
        (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i *
            rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 l +
          rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 i *
            rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M l -
          if i = l then
            rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 i
          else 0) +
      eulerDerivative (eulerDerivative phi) * Polynomial.C
        (rankThreeIntegralLineDirection (K := K)
            v2 v3 v4 u1 u2 u3 u4 i *
          rankThreeIntegralLineDirection (K := K)
            v2 v3 v4 u1 u2 u3 u4 l) := by
  by_cases hil : i = l
  · subst l
    simp [rankThreePolynomialMomentHessian, lineMomentHessian]
  · simp [rankThreePolynomialMomentHessian, lineMomentHessian, hil]

/-- Coefficient formula for the rank-three polynomial moment matrix. -/
theorem coeff_rankThreePolynomialMomentHessian
    {K : Type*} [Field K] [CharZero K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) (i l : Fin 4) (j : ℕ) :
    (rankThreePolynomialMomentHessian
        v2 v3 v4 u1 u2 u3 u4 M phi i l).coeff j =
      phi.coeff j *
        ((rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
            (j : K) * rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 i) *
          (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M l +
            (j : K) * rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 l) -
          if i = l then
            rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
              (j : K) * rankThreeIntegralLineDirection (K := K)
                v2 v3 v4 u1 u2 u3 u4 i
          else 0) := by
  rw [rankThreePolynomialMomentHessian_apply]
  simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C, coeff_eulerDerivative]
  by_cases hil : i = l <;> simp [hil] <;> ring

/-- Raw support-sum form of one rank-three moment entry. -/
def rankThreeRawMomentEntry
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) (i l : Fin 4) : Polynomial K :=
  phi.sum fun j c =>
    Polynomial.C
      (c *
        ((rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
            (j : K) * rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 i) *
          (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M l +
            (j : K) * rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 l) -
          if i = l then
            rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
              (j : K) * rankThreeIntegralLineDirection (K := K)
                v2 v3 v4 u1 u2 u3 u4 i
          else 0)) * Polynomial.X ^ j

/-- Coefficients of the raw support-sum entry. -/
theorem coeff_rankThreeRawMomentEntry
    {K : Type*} [Field K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) (i l : Fin 4) (r : ℕ) :
    (rankThreeRawMomentEntry
        v2 v3 v4 u1 u2 u3 u4 M phi i l).coeff r =
      phi.coeff r *
        ((rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
            (r : K) * rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 i) *
          (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M l +
            (r : K) * rankThreeIntegralLineDirection (K := K)
              v2 v3 v4 u1 u2 u3 u4 l) -
          if i = l then
            rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
              (r : K) * rankThreeIntegralLineDirection (K := K)
                v2 v3 v4 u1 u2 u3 u4 i
          else 0) := by
  classical
  unfold rankThreeRawMomentEntry
  rw [Polynomial.sum_def, Polynomial.finset_sum_coeff]
  by_cases hr : r ∈ phi.support
  · rw [Finset.sum_eq_single r]
    · simp only [Polynomial.coeff_C_mul_X_pow, if_pos]
    · intro b hb hbr
      have hrb : r ≠ b := Ne.symm hbr
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp [hrb]
    · intro hnot
      exact (hnot hr).elim
  · have hcoeff : phi.coeff r = 0 := by
      simpa [Polynomial.mem_support_iff] using hr
    have hsum :
        (∑ n ∈ phi.support,
          (Polynomial.C
            (phi.coeff n *
              ((rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
                  (n : K) * rankThreeIntegralLineDirection (K := K)
                    v2 v3 v4 u1 u2 u3 u4 i) *
                (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M l +
                  (n : K) * rankThreeIntegralLineDirection (K := K)
                    v2 v3 v4 u1 u2 u3 u4 l) -
                if i = l then
                  rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i +
                    (n : K) * rankThreeIntegralLineDirection (K := K)
                      v2 v3 v4 u1 u2 u3 u4 i
                else 0)) * Polynomial.X ^ n).coeff r) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hrb : r ≠ b := by
        intro h
        apply hr
        simpa [h] using hb
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp [hrb]
    rw [hsum, hcoeff]
    simp

/-- The raw support-sum entry is exactly the rank-three moment entry. -/
theorem rankThreeRawMomentEntry_eq_moment
    {K : Type*} [Field K] [CharZero K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (phi : Polynomial K) (i l : Fin 4) :
    rankThreeRawMomentEntry v2 v3 v4 u1 u2 u3 u4 M phi i l =
      rankThreePolynomialMomentHessian
        v2 v3 v4 u1 u2 u3 u4 M phi i l := by
  apply Polynomial.ext
  intro r
  rw [coeff_rankThreeRawMomentEntry,
    coeff_rankThreePolynomialMomentHessian]

/-- Raw form of the central rank-three specialisation theorem. -/
theorem rankThreeLineSpecialisation_eulerScaledHessian_raw
    {K : Type*} [Field K] [CharZero K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    rankThreeLineSpecialisation.mapMatrix
      (eulerScaledHessian
        (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi)) =
      (Polynomial.X ^ u1).compRingHom.mapMatrix
        (Matrix.of fun i l =>
          rankThreeRawMomentEntry
            v2 v3 v4 u1 u2 u3 u4 M phi i l) := by
  apply Matrix.ext
  intro i l
  change
    rankThreeLineSpecialisation
        (eulerScaledHessian
          (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi) i l) =
      (Polynomial.X ^ u1).compRingHom
        (rankThreeRawMomentEntry
          v2 v3 v4 u1 u2 u3 u4 M phi i l)
  simp only [rankThreeLinePolynomial, Polynomial.sum_def]
  rw [eulerScaledHessian_sum]
  rw [map_sum]
  unfold rankThreeRawMomentEntry
  simp only [Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjM : j ≤ M := support_le_of_natDegree_le hdeg hj
  rw [rankThreeLineSpecialisation_eulerScaledHessian_term]
  have he := rankThreeLineExponentValue_eq_affine
    (K := K) v2 v3 v4 u1 u2 u3 u4 M j hjM
  have hei := congrFun he i
  have hel := congrFun he l
  rw [hei, hel]
  simp [Polynomial.coe_compRingHom_apply, pow_mul]
  by_cases hil : i = l <;> simp [hil]
  <;> ring

/-- Central realisation theorem: the specialised Euler-scaled Hessian of the
honest rank-three line is the rank-three moment matrix after `X -> X^u1`. -/
theorem rankThreeLineSpecialisation_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    rankThreeLineSpecialisation.mapMatrix
      (eulerScaledHessian
        (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi)) =
      (Polynomial.X ^ u1).compRingHom.mapMatrix
        (rankThreePolynomialMomentHessian
          v2 v3 v4 u1 u2 u3 u4 M phi) := by
  rw [rankThreeLineSpecialisation_eulerScaledHessian_raw hdeg]
  apply congrArg ((Polynomial.X ^ u1).compRingHom.mapMatrix)
  apply Matrix.ext
  intro i l
  exact rankThreeRawMomentEntry_eq_moment
    v2 v3 v4 u1 u2 u3 u4 M phi i l

/-- Determinant form of the central realisation theorem. -/
theorem rankThreeLineSpecialisation_det_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    rankThreeLineSpecialisation
        ((eulerScaledHessian
          (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi)).det) =
      ((rankThreePolynomialMomentHessian
          v2 v3 v4 u1 u2 u3 u4 M phi).det).comp
        (Polynomial.X ^ u1) := by
  let s : MvPolynomial (Fin 4) K →+* Polynomial K :=
    rankThreeLineSpecialisation
  let c : Polynomial K →+* Polynomial K :=
    (Polynomial.X ^ u1).compRingHom
  have hm := rankThreeLineSpecialisation_eulerScaledHessian
    (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
    (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
    (M := M) (phi := phi) hdeg
  have hsdet := congrArg Matrix.det hm
  rw [← RingHom.map_det s, ← RingHom.map_det c] at hsdet
  simpa [s, c, Polynomial.coe_compRingHom_apply] using hsdet

/-- Zero ordinary Hessian determinant gives zero specialised Euler determinant. -/
theorem rankThreeLineSpecialisation_euler_det_zero_of_hessianDeterminant_zero
    {K : Type*} [Field K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hdet : hessianDeterminant
      (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi) = 0) :
    rankThreeLineSpecialisation
      ((eulerScaledHessian
        (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi)).det) = 0 := by
  rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant]
  rw [hdet]
  simp

/-- Therefore a zero Hessian determinant of the honest rank-three line gives a
zero polynomial moment determinant whenever the line genuinely leaves the
omitted coordinate. -/
theorem rankThreePolynomialMoment_det_zero_of_hessianDeterminant_zero
    {K : Type*} [Field K] [CharZero K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hu1 : 0 < u1)
    (hdeg : phi.natDegree ≤ M)
    (hdet : hessianDeterminant
      (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi) = 0) :
    (rankThreePolynomialMomentHessian
      v2 v3 v4 u1 u2 u3 u4 M phi).det = 0 := by
  have hs := rankThreeLineSpecialisation_euler_det_zero_of_hessianDeterminant_zero
    (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
    (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
    (M := M) (phi := phi) hdet
  rw [rankThreeLineSpecialisation_det_eulerScaledHessian
    (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
    (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
    (M := M) (phi := phi) hdeg] at hs
  exact comp_X_pow_eq_zero_of_pos hu1 hs

/-- Mapping a zero polynomial moment determinant to the fraction field gives
the rank-three fraction-moment predicate with the integral endpoint data. -/
theorem rankThreeFractionMomentDetZero_of_polynomialMoment_det_zero
    {K : Type*} [Field K] [CharZero K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hdet :
      (rankThreePolynomialMomentHessian
        v2 v3 v4 u1 u2 u3 u4 M phi).det = 0) :
    RankThreeFractionMomentDetZero
      phi
      ((M * v2 : ℕ) : K)
      ((M * v3 : ℕ) : K)
      ((M * v4 : ℕ) : K)
      (u1 : K)
      ((u2 : K) - (v2 : K))
      ((u3 : K) - (v3 : K))
      ((u4 : K) - (v4 : K)) := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  have hmapped :
      (ι.mapMatrix (rankThreePolynomialMomentHessian
        v2 v3 v4 u1 u2 u3 u4 M phi)).det = 0 := by
    rw [← RingHom.map_det ι]
    simpa using congrArg ι hdet
  have hbase :
      (fun i => ι (Polynomial.C
        (rankThreeIntegralLineBaseExponent (K := K) v2 v3 v4 M i))) =
        rankThreeLogBaseExponent
          (ι (Polynomial.C (((M * v2 : ℕ) : K))))
          (ι (Polynomial.C (((M * v3 : ℕ) : K))))
          (ι (Polynomial.C (((M * v4 : ℕ) : K)))) := by
    funext i
    fin_cases i <;>
      simp [rankThreeIntegralLineBaseExponent, rankThreeLogBaseExponent, F, ι]
  have hdir :
      (fun i => ι (Polynomial.C
        (rankThreeIntegralLineDirection (K := K)
          v2 v3 v4 u1 u2 u3 u4 i))) =
        rankThreeLogDirection
          (ι (Polynomial.C (u1 : K)))
          (ι (Polynomial.C ((u2 : K) - (v2 : K))))
          (ι (Polynomial.C ((u3 : K) - (v3 : K))))
          (ι (Polynomial.C ((u4 : K) - (v4 : K)))) := by
    funext i
    fin_cases i <;>
      simp [rankThreeIntegralLineDirection, rankThreeLogDirection, F, ι]
  have hmat :
      ι.mapMatrix (rankThreePolynomialMomentHessian
        v2 v3 v4 u1 u2 u3 u4 M phi) =
        lineMomentHessian
          (rankThreeLogBaseExponent
            (ι (Polynomial.C (((M * v2 : ℕ) : K))))
            (ι (Polynomial.C (((M * v3 : ℕ) : K))))
            (ι (Polynomial.C (((M * v4 : ℕ) : K)))))
          (rankThreeLogDirection
            (ι (Polynomial.C (u1 : K)))
            (ι (Polynomial.C ((u2 : K) - (v2 : K))))
            (ι (Polynomial.C ((u3 : K) - (v3 : K))))
            (ι (Polynomial.C ((u4 : K) - (v4 : K)))))
          (ι phi) (ι (eulerDerivative phi))
          (ι (eulerDerivative (eulerDerivative phi))) := by
    unfold rankThreePolynomialMomentHessian
    rw [mapMatrix_lineMomentHessian]
    rw [hbase, hdir]
  unfold RankThreeFractionMomentDetZero
  dsimp
  rw [← hmat]
  exact hmapped

/-- **End-to-end honest rank-three line bridge.**
A genuine rank-three endpoint line with zero multivariate Hessian determinant
produces exactly the fraction-core determinant equation consumed by the mature
rank-three rational-rigidity stack. -/
theorem rankThreeFractionCoreDetZero_of_line_hessianDeterminant_zero
    {K : Type*} [Field K] [CharZero K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hu1 : 0 < u1)
    (hphi : phi ≠ 0)
    (hdeg : phi.natDegree ≤ M)
    (hdet : hessianDeterminant
      (rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi) = 0) :
    RankThreeFractionCoreDetZero
      phi
      ((M * v2 : ℕ) : K)
      ((M * v3 : ℕ) : K)
      ((M * v4 : ℕ) : K)
      (u1 : K)
      ((u2 : K) - (v2 : K))
      ((u3 : K) - (v3 : K))
      ((u4 : K) - (v4 : K)) := by
  have hpoly :=
    rankThreePolynomialMoment_det_zero_of_hessianDeterminant_zero
      (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
      (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
      (M := M) (phi := phi) hu1 hdeg hdet
  have hmoment :=
    rankThreeFractionMomentDetZero_of_polynomialMoment_det_zero
      (K := K) (v2 := v2) (v3 := v3) (v4 := v4)
      (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4)
      (M := M) (phi := phi) hpoly
  exact rankThree_fraction_core_det_zero_of_moment_det_zero
    hphi hmoment

end

end HC4.Polynomial
