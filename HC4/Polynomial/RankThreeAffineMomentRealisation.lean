import HC4.Polynomial.RankThreeAffineLineRealisation
import HC4.Polynomial.RankThreeFractionMomentBridge
import Mathlib.Tactic

/-!
# A18.5.25: generic honest affine edge to rank-three fraction core

A18.5.24 supplies an honest multivariate polynomial whose supported exponents
cast to `v + j w`, with `v=(0,A,B,C)`.  The generic logarithmic-moment algebra
already knows how to analyse such a line.  This file identifies the
specialised Euler-scaled Hessian of the actual polynomial with that moment
matrix after the injective substitution `X -> X^u1`.

Unlike A18.5.6, no finite-segment divisibility or natural transverse direction
is required.  The transverse direction entries may be arbitrary field
values; only the omitted-coordinate step is a positive natural number.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- Polynomial-valued moment Hessian for a general affine rank-three line. -/
def rankThreeAffinePolynomialMomentHessian
    {K : Type*} [Field K]
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  lineMomentHessian
    (fun i => Polynomial.C
      (rankThreeLogBaseExponent (A : K) (B : K) (C : K) i))
    (fun i => Polynomial.C
      (rankThreeLogDirection (u1 : K) q r s i))
    phi (eulerDerivative phi) (eulerDerivative (eulerDerivative phi))

/-- Entrywise normal form of the general polynomial moment Hessian. -/
theorem rankThreeAffinePolynomialMomentHessian_apply
    {K : Type*} [Field K]
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K)
    (i l : Fin 4) :
    rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi i l =
      phi * Polynomial.C
        (rankThreeLogBaseExponent (A : K) (B : K) (C : K) i *
            rankThreeLogBaseExponent (A : K) (B : K) (C : K) l -
          if i = l then rankThreeLogBaseExponent (A : K) (B : K) (C : K) i
          else 0) +
      eulerDerivative phi * Polynomial.C
        (rankThreeLogBaseExponent (A : K) (B : K) (C : K) i *
            rankThreeLogDirection (u1 : K) q r s l +
          rankThreeLogDirection (u1 : K) q r s i *
            rankThreeLogBaseExponent (A : K) (B : K) (C : K) l -
          if i = l then rankThreeLogDirection (u1 : K) q r s i else 0) +
      eulerDerivative (eulerDerivative phi) * Polynomial.C
        (rankThreeLogDirection (u1 : K) q r s i *
          rankThreeLogDirection (u1 : K) q r s l) := by
  by_cases hil : i = l
  · subst l
    simp [rankThreeAffinePolynomialMomentHessian, lineMomentHessian]
  · simp [rankThreeAffinePolynomialMomentHessian, lineMomentHessian, hil]

/-- Coefficient formula for the general polynomial moment Hessian. -/
theorem coeff_rankThreeAffinePolynomialMomentHessian
    {K : Type*} [Field K] [CharZero K]
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K)
    (i l : Fin 4) (j : ℕ) :
    (rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi i l).coeff j =
      phi.coeff j *
        ((rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
            (j : K) * rankThreeLogDirection (u1 : K) q r s i) *
          (rankThreeLogBaseExponent (A : K) (B : K) (C : K) l +
            (j : K) * rankThreeLogDirection (u1 : K) q r s l) -
          if i = l then
            rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
              (j : K) * rankThreeLogDirection (u1 : K) q r s i
          else 0) := by
  rw [rankThreeAffinePolynomialMomentHessian_apply]
  simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C, coeff_eulerDerivative]
  by_cases hil : i = l <;> simp [hil] <;> ring

/-- Raw support-sum form of one general affine moment entry. -/
def rankThreeAffineRawMomentEntry
    {K : Type*} [Field K]
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K)
    (i l : Fin 4) : Polynomial K :=
  phi.sum fun j c =>
    Polynomial.C
      (c *
        ((rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
            (j : K) * rankThreeLogDirection (u1 : K) q r s i) *
          (rankThreeLogBaseExponent (A : K) (B : K) (C : K) l +
            (j : K) * rankThreeLogDirection (u1 : K) q r s l) -
          if i = l then
            rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
              (j : K) * rankThreeLogDirection (u1 : K) q r s i
          else 0)) * Polynomial.X ^ j

/-- Coefficients of the raw support-sum moment entry. -/
theorem coeff_rankThreeAffineRawMomentEntry
    {K : Type*} [Field K]
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K)
    (i l : Fin 4) (n : ℕ) :
    (rankThreeAffineRawMomentEntry A B C u1 q r s phi i l).coeff n =
      phi.coeff n *
        ((rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
            (n : K) * rankThreeLogDirection (u1 : K) q r s i) *
          (rankThreeLogBaseExponent (A : K) (B : K) (C : K) l +
            (n : K) * rankThreeLogDirection (u1 : K) q r s l) -
          if i = l then
            rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
              (n : K) * rankThreeLogDirection (u1 : K) q r s i
          else 0) := by
  classical
  unfold rankThreeAffineRawMomentEntry
  rw [Polynomial.sum_def, Polynomial.finset_sum_coeff]
  by_cases hn : n ∈ phi.support
  · rw [Finset.sum_eq_single n]
    · simp only [Polynomial.coeff_C_mul_X_pow, if_pos]
    · intro j hj hnj
      have hjn : n ≠ j := Ne.symm hnj
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp [hjn]
    · intro hnot
      exact (hnot hn).elim
  · have hcoeff : phi.coeff n = 0 := by
      simpa [Polynomial.mem_support_iff] using hn
    have hsum :
        (∑ j ∈ phi.support,
          (Polynomial.C
            (phi.coeff j *
              ((rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
                  (j : K) * rankThreeLogDirection (u1 : K) q r s i) *
                (rankThreeLogBaseExponent (A : K) (B : K) (C : K) l +
                  (j : K) * rankThreeLogDirection (u1 : K) q r s l) -
                if i = l then
                  rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
                    (j : K) * rankThreeLogDirection (u1 : K) q r s i
                else 0)) * Polynomial.X ^ j).coeff n) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hnj : n ≠ j := by
        intro h
        apply hn
        simpa [h] using hj
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp [hnj]
    rw [hsum, hcoeff]
    simp

/-- The raw support sum is exactly the polynomial line-moment entry. -/
theorem rankThreeAffineRawMomentEntry_eq_moment
    {K : Type*} [Field K] [CharZero K]
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K)
    (i l : Fin 4) :
    rankThreeAffineRawMomentEntry A B C u1 q r s phi i l =
      rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi i l := by
  apply Polynomial.ext
  intro n
  rw [coeff_rankThreeAffineRawMomentEntry,
    coeff_rankThreeAffinePolynomialMomentHessian]

/-- Raw central realisation theorem for an honest general affine line. -/
theorem RankThreeAffineLineData.specialisation_eulerScaledHessian_raw
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi) :
    rankThreeLineSpecialisation.mapMatrix
        (eulerScaledHessian L.polynomial) =
      (Polynomial.X ^ u1).compRingHom.mapMatrix
        (Matrix.of fun i l =>
          rankThreeAffineRawMomentEntry A B C u1 q r s phi i l) := by
  apply Matrix.ext
  intro i l
  change
    rankThreeLineSpecialisation (eulerScaledHessian L.polynomial i l) =
      (Polynomial.X ^ u1).compRingHom
        (rankThreeAffineRawMomentEntry A B C u1 q r s phi i l)
  simp only [RankThreeAffineLineData.polynomial, Polynomial.sum_def]
  rw [eulerScaledHessian_sum]
  rw [map_sum]
  unfold rankThreeAffineRawMomentEntry
  simp only [Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [L.specialisation_eulerScaledHessian_term hj]
  simp [Polynomial.coe_compRingHom_apply, pow_mul]
  by_cases hil : i = l <;> simp [hil] <;> ring

/-- Central realisation theorem: specialised honest Euler-Hessian equals the
general polynomial moment Hessian after `X -> X^u1`. -/
theorem RankThreeAffineLineData.specialisation_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi) :
    rankThreeLineSpecialisation.mapMatrix
        (eulerScaledHessian L.polynomial) =
      (Polynomial.X ^ u1).compRingHom.mapMatrix
        (rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi) := by
  rw [L.specialisation_eulerScaledHessian_raw]
  apply congrArg ((Polynomial.X ^ u1).compRingHom.mapMatrix)
  apply Matrix.ext
  intro i l
  exact rankThreeAffineRawMomentEntry_eq_moment A B C u1 q r s phi i l

/-- Determinant form of the central affine-line realisation theorem. -/
theorem RankThreeAffineLineData.specialisation_det_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi) :
    rankThreeLineSpecialisation ((eulerScaledHessian L.polynomial).det) =
      ((rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi).det).comp
        (Polynomial.X ^ u1) := by
  let sp : MvPolynomial (Fin 4) K →+* Polynomial K := rankThreeLineSpecialisation
  let cp : Polynomial K →+* Polynomial K := (Polynomial.X ^ u1).compRingHom
  have hm := L.specialisation_eulerScaledHessian
  have hsdet := congrArg Matrix.det hm
  rw [← RingHom.map_det sp, ← RingHom.map_det cp] at hsdet
  simpa [sp, cp, Polynomial.coe_compRingHom_apply] using hsdet

/-- Zero ordinary Hessian determinant of the honest affine polynomial forces
zero determinant of its polynomial moment matrix. -/
theorem RankThreeAffineLineData.polynomialMoment_det_zero_of_hessian_zero
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (hu1 : 0 < u1)
    (hdet : hessianDeterminant L.polynomial = 0) :
    (rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi).det = 0 := by
  have hs :
      rankThreeLineSpecialisation ((eulerScaledHessian L.polynomial).det) = 0 := by
    rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant]
    rw [hdet]
    simp
  rw [L.specialisation_det_eulerScaledHessian] at hs
  exact comp_X_pow_eq_zero_of_pos hu1 hs

/-- Mapping the polynomial moment determinant to the fraction field gives the
standard rank-three fraction-moment predicate. -/
theorem rankThreeAffineFractionMomentDetZero_of_polynomialMoment_det_zero
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (hdet :
      (rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi).det = 0) :
    RankThreeFractionMomentDetZero
      phi (A : K) (B : K) (C : K) (u1 : K) q r s := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  have hmapped :
      (ι.mapMatrix
        (rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi)).det = 0 := by
    rw [← RingHom.map_det ι]
    simpa using congrArg ι hdet
  have hbase :
      (fun i => ι (Polynomial.C
        (rankThreeLogBaseExponent (A : K) (B : K) (C : K) i))) =
        rankThreeLogBaseExponent
          (ι (Polynomial.C (A : K)))
          (ι (Polynomial.C (B : K)))
          (ι (Polynomial.C (C : K))) := by
    funext i
    fin_cases i <;>
      simp [rankThreeLogBaseExponent, F, ι] <;> ring
  have hdir :
      (fun i => ι (Polynomial.C
        (rankThreeLogDirection (u1 : K) q r s i))) =
        rankThreeLogDirection
          (ι (Polynomial.C (u1 : K)))
          (ι (Polynomial.C q))
          (ι (Polynomial.C r))
          (ι (Polynomial.C s)) := by
    funext i
    fin_cases i <;>
      simp [rankThreeLogDirection, F, ι] <;> ring
  have hmat :
      ι.mapMatrix (rankThreeAffinePolynomialMomentHessian A B C u1 q r s phi) =
        lineMomentHessian
          (rankThreeLogBaseExponent
            (ι (Polynomial.C (A : K)))
            (ι (Polynomial.C (B : K)))
            (ι (Polynomial.C (C : K))))
          (rankThreeLogDirection
            (ι (Polynomial.C (u1 : K)))
            (ι (Polynomial.C q))
            (ι (Polynomial.C r))
            (ι (Polynomial.C s)))
          (ι phi) (ι (eulerDerivative phi))
          (ι (eulerDerivative (eulerDerivative phi))) := by
    unfold rankThreeAffinePolynomialMomentHessian
    rw [mapMatrix_lineMomentHessian]
    rw [hbase, hdir]
  unfold RankThreeFractionMomentDetZero
  dsimp
  rw [← hmat]
  exact hmapped

/-- **End-to-end generic affine line bridge.**
A genuine honest affine rank-three edge with zero multivariate Hessian
determinant produces exactly the fraction-core equation consumed by the mature
rank-three rational-rigidity stack. -/
theorem RankThreeAffineLineData.fractionCoreDetZero_of_hessian_zero
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (hu1 : 0 < u1)
    (hphi : phi ≠ 0)
    (hdet : hessianDeterminant L.polynomial = 0) :
    RankThreeFractionCoreDetZero
      phi (A : K) (B : K) (C : K) (u1 : K) q r s := by
  have hpoly := L.polynomialMoment_det_zero_of_hessian_zero hu1 hdet
  have hmoment :=
    rankThreeAffineFractionMomentDetZero_of_polynomialMoment_det_zero hpoly
  exact rankThree_fraction_core_det_zero_of_moment_det_zero hphi hmoment

end

end HC4.Polynomial