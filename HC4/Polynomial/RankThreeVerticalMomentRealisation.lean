import HC4.Polynomial.RankThreeVerticalLine
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# A18.5.11: vertical rank-three line to the fraction core

A18.5.10 introduced the honest vertical line

    F = x₁^b x₂^c x₃^d φ(x₀).

The mature A18.5.5--A18.5.6 moment machinery already contains exactly the
matrix needed here.  Set

    M = 1,
    v = (b,c,d),
    u = (1,b,c,d).

Then the integral rank-three base is `(0,b,c,d)` and the affine direction is
`(1,0,0,0)`.  Unlike the finite-segment model, no upper bound on
`natDegree φ` is needed: every vertical exponent `(j,b,c,d)` is honest for
all `j`.

This file proves that the specialised Euler-scaled Hessian of the vertical
polynomial is exactly that existing polynomial moment matrix.  Hence zero
ordinary Hessian determinant gives the rank-three fraction-core equation with
parameters

    (v₂,v₃,v₄,w₁,w₂,w₃,w₄) = (b,c,d,1,0,0,0).
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- The vertical exponent is the existing rank-three affine exponent with
base `(0,b,c,d)` and direction `(1,0,0,0)`. -/
theorem rankThreeVerticalExponentValue_eq_affine
    {K : Type*} [Field K] [CharZero K]
    (b c d j : ℕ) :
    rankThreeVerticalExponentValue (K := K) b c d j =
      fun i =>
        rankThreeIntegralLineBaseExponent (K := K) b c d 1 i +
          (j : K) *
            rankThreeIntegralLineDirection (K := K)
              b c d 1 b c d i := by
  funext i
  fin_cases i <;>
    simp [rankThreeVerticalExponentValue,
      rankThreeIntegralLineBaseExponent,
      rankThreeIntegralLineDirection,
      rankThreeLogBaseExponent, rankThreeLogDirection] <;>
    ring

/-- Specialised Euler-Hessian formula for one vertical term. -/
theorem rankThreeLineSpecialisation_eulerScaledHessian_verticalTerm
    {K : Type*} [Field K] [CharZero K]
    (b c d j : ℕ) (a : K) (i l : Fin 4) :
    rankThreeLineSpecialisation
        (eulerScaledHessian (rankThreeVerticalTerm b c d j a) i l) =
      Polynomial.C
          (rankThreeVerticalExponentValue (K := K) b c d j i *
            rankThreeVerticalExponentValue (K := K) b c d j l -
            if i = l then
              rankThreeVerticalExponentValue (K := K) b c d j i
            else 0) *
        (Polynomial.C a * Polynomial.X ^ j) := by
  rw [eulerScaledHessian_rankThreeVerticalTerm]
  rw [map_mul]
  rw [rankThreeLineSpecialisation_verticalTerm]
  have hC :
      rankThreeLineSpecialisation
        (MvPolynomial.C
          (rankThreeVerticalExponentValue (K := K) b c d j i *
            rankThreeVerticalExponentValue (K := K) b c d j l -
            if i = l then
              rankThreeVerticalExponentValue (K := K) b c d j i
            else 0)) =
        Polynomial.C
          (rankThreeVerticalExponentValue (K := K) b c d j i *
            rankThreeVerticalExponentValue (K := K) b c d j l -
            if i = l then
              rankThreeVerticalExponentValue (K := K) b c d j i
            else 0) := by
    simp [rankThreeLineSpecialisation]
  rw [hC]

/-- Raw realisation: the specialised Euler-scaled Hessian of the honest
vertical line is the support-sum form of the existing rank-three moment
matrix. -/
theorem rankThreeVerticalSpecialisation_eulerScaledHessian_raw
    {K : Type*} [Field K] [CharZero K]
    (b c d : ℕ) (phi : Polynomial K) :
    rankThreeLineSpecialisation.mapMatrix
      (eulerScaledHessian (rankThreeVerticalPolynomial b c d phi)) =
        Matrix.of fun i l =>
          rankThreeRawMomentEntry b c d 1 b c d 1 phi i l := by
  apply Matrix.ext
  intro i l
  change
    rankThreeLineSpecialisation
        (eulerScaledHessian
          (rankThreeVerticalPolynomial b c d phi) i l) =
      rankThreeRawMomentEntry b c d 1 b c d 1 phi i l
  simp only [rankThreeVerticalPolynomial, Polynomial.sum_def]
  rw [eulerScaledHessian_sum]
  rw [map_sum]
  unfold rankThreeRawMomentEntry
  simp only [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rankThreeLineSpecialisation_eulerScaledHessian_verticalTerm]
  have he := rankThreeVerticalExponentValue_eq_affine
    (K := K) b c d j
  have hei := congrFun he i
  have hel := congrFun he l
  rw [hei, hel]
  by_cases hil : i = l <;> simp [hil] <;> ring

/-- Central vertical realisation theorem.  The existing polynomial moment
matrix with `M=1` and equal transverse endpoints is literally the specialised
Euler Hessian of `x₁^b x₂^c x₃^d φ(x₀)`. -/
theorem rankThreeVerticalSpecialisation_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    (b c d : ℕ) (phi : Polynomial K) :
    rankThreeLineSpecialisation.mapMatrix
      (eulerScaledHessian (rankThreeVerticalPolynomial b c d phi)) =
        rankThreePolynomialMomentHessian b c d 1 b c d 1 phi := by
  rw [rankThreeVerticalSpecialisation_eulerScaledHessian_raw]
  apply Matrix.ext
  intro i l
  exact rankThreeRawMomentEntry_eq_moment
    b c d 1 b c d 1 phi i l

/-- Determinant form of the vertical realisation theorem. -/
theorem rankThreeVerticalSpecialisation_det_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    (b c d : ℕ) (phi : Polynomial K) :
    rankThreeLineSpecialisation
      ((eulerScaledHessian (rankThreeVerticalPolynomial b c d phi)).det) =
        (rankThreePolynomialMomentHessian b c d 1 b c d 1 phi).det := by
  let s : MvPolynomial (Fin 4) K →+* Polynomial K :=
    rankThreeLineSpecialisation
  have hm := rankThreeVerticalSpecialisation_eulerScaledHessian
    (K := K) b c d phi
  have hsdet := congrArg Matrix.det hm
  rw [← RingHom.map_det s] at hsdet
  simpa [s] using hsdet

/-- Zero ordinary Hessian determinant gives zero specialised Euler
determinant for the vertical line. -/
theorem rankThreeVerticalSpecialisation_euler_det_zero_of_hessianDeterminant_zero
    {K : Type*} [Field K]
    {b c d : ℕ} {phi : Polynomial K}
    (hdet : hessianDeterminant (rankThreeVerticalPolynomial b c d phi) = 0) :
    rankThreeLineSpecialisation
      ((eulerScaledHessian (rankThreeVerticalPolynomial b c d phi)).det) = 0 := by
  rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant]
  rw [hdet]
  simp

/-- Hence a singular honest vertical line gives a zero polynomial moment
determinant, with no degree bound on `φ`. -/
theorem rankThreeVerticalPolynomialMoment_det_zero_of_hessianDeterminant_zero
    {K : Type*} [Field K] [CharZero K]
    {b c d : ℕ} {phi : Polynomial K}
    (hdet : hessianDeterminant (rankThreeVerticalPolynomial b c d phi) = 0) :
    (rankThreePolynomialMomentHessian b c d 1 b c d 1 phi).det = 0 := by
  have hs :=
    rankThreeVerticalSpecialisation_euler_det_zero_of_hessianDeterminant_zero
      (K := K) (b := b) (c := c) (d := d) (phi := phi) hdet
  rw [rankThreeVerticalSpecialisation_det_eulerScaledHessian
    (K := K) b c d phi] at hs
  exact hs

/-- **End-to-end vertical rank-three bridge.**
A nonzero vertical coefficient polynomial whose honest four-variable line has
zero Hessian determinant produces exactly the mature fraction-core equation
with base `(0,b,c,d)` and direction `(1,0,0,0)`. -/
theorem rankThreeFractionCoreDetZero_of_vertical_hessianDeterminant_zero
    {K : Type*} [Field K] [CharZero K]
    {b c d : ℕ} {phi : Polynomial K}
    (hphi : phi ≠ 0)
    (hdet : hessianDeterminant (rankThreeVerticalPolynomial b c d phi) = 0) :
    RankThreeFractionCoreDetZero
      phi (b : K) (c : K) (d : K) 1 0 0 0 := by
  have hpoly :=
    rankThreeVerticalPolynomialMoment_det_zero_of_hessianDeterminant_zero
      (K := K) (b := b) (c := c) (d := d) (phi := phi) hdet
  have hmomentRaw :=
    rankThreeFractionMomentDetZero_of_polynomialMoment_det_zero
      (K := K)
      (v2 := b) (v3 := c) (v4 := d)
      (u1 := 1) (u2 := b) (u3 := c) (u4 := d)
      (M := 1) (phi := phi) hpoly
  have hmoment :
      RankThreeFractionMomentDetZero
        phi (b : K) (c : K) (d : K) 1 0 0 0 := by
    simpa using hmomentRaw
  exact rankThree_fraction_core_det_zero_of_moment_det_zero hphi hmoment

end

end HC4.Polynomial
