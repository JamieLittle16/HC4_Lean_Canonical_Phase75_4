import HC4.Polynomial.CodimensionTwoPrimitiveDeparturePencil
import Mathlib.Tactic

/-!
# Coefficient-weighted codimension-two departure pencil

The honest A19 carrier has nonzero coefficients on its base monomial and the
two first departures.  This file keeps those coefficients explicit instead of
normalising them away.

For exponent cores `M(v),M(u),M(w)` and coefficients `C,A,B`, the pencil is

    C M(v) + s A M(u) + t B M(w).

A determinant term of bidegree `(r,q)` uses exactly `r` copies of the `u`
block, `q` copies of the `w` block, and `4-r-q` copies of the base block, so
the primitive-departure factors from the unweighted pencil acquire only the
corresponding harmless powers of `A,B,C`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

private def nestedCw {K : Type*} [CommRing K]
    (x : K) : Polynomial (Polynomial K) :=
  Polynomial.C (Polynomial.C x)

private def sVarw {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.X

private def tVarw {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.C Polynomial.X

/-- Coefficient-weighted version of `codimensionTwoDeparturePencil`. -/
noncomputable def codimensionTwoWeightedDeparturePencil
    {K : Type*} [CommRing K]
    (D p a m c n C A B : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  Matrix.of fun i j =>
    nestedCw C * nestedCw
        (vectorHessianCore (K := K) ![p, D-p, 0, 0] i j) +
      sVarw * nestedCw A * nestedCw
        (vectorHessianCore (K := K) ![a, D-m-a, m, 0] i j) +
      tVarw * nestedCw B * nestedCw
        (vectorHessianCore (K := K) ![c, D-n-c, 0, n] i j)

set_option maxHeartbeats 5000000 in
/-- First mixed coefficient, retaining all three source coefficients. -/
theorem coeff_s_t_det_codimensionTwoWeightedDeparturePencil
    {K : Type*} [CommRing K]
    (D p a m c n C A B : K) :
    (((codimensionTwoWeightedDeparturePencil
      D p a m c n C A B).det).coeff 1).coeff 1 =
      C^2 * A * B *
        (m * n * p * (p-D) * (D-1) * (m-1) * (n-1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoWeightedDeparturePencil, nestedCw, sVarw, tVarw,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 5000000 in
/-- Doubly primitive square channel. -/
theorem coeff_s_sq_t_sq_det_codimensionTwoWeightedDeparturePencil_primitive
    {K : Type*} [CommRing K]
    (D p a c C A B : K) :
    (((codimensionTwoWeightedDeparturePencil
      D p a 1 c 1 C A B).det).coeff 2).coeff 2 =
      A^2 * B^2 * (D-1)^2 * (a-c)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoWeightedDeparturePencil, nestedCw, sVarw, tVarw,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 5000000 in
/-- Left-primitive endpoint channel. -/
theorem coeff_s_cube_t_det_codimensionTwoWeightedDeparturePencil_leftPrimitive
    {K : Type*} [CommRing K]
    (D p a c n C A B : K) :
    (((codimensionTwoWeightedDeparturePencil
      D p a 1 c n C A B).det).coeff 3).coeff 1 =
      A^3 * B * (a * n * (D-1) * (n-1) * (D-a-1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoWeightedDeparturePencil, nestedCw, sVarw, tVarw,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 5000000 in
/-- Lower asymmetric `s^2 t` channel. -/
theorem coeff_s_sq_t_det_codimensionTwoWeightedDeparturePencil_leftZero
    {K : Type*} [CommRing K]
    (D p c n C A B : K) :
    (((codimensionTwoWeightedDeparturePencil
      D p 0 1 c n C A B).det).coeff 2).coeff 1 =
      -(C * A^2 * B *
        (n * (n-1) * p * (D-1)^2 * (p-1))) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoWeightedDeparturePencil, nestedCw, sVarw, tVarw,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 5000000 in
/-- Upper asymmetric `s^2 t` channel. -/
theorem coeff_s_sq_t_det_codimensionTwoWeightedDeparturePencil_leftTop
    {K : Type*} [CommRing K]
    (D p c n C A B : K) :
    (((codimensionTwoWeightedDeparturePencil
      D p (D-1) 1 c n C A B).det).coeff 2).coeff 1 =
      -(C * A^2 * B *
        (n * (n-1) * (D-1)^2 * (p-D) * (p-D+1))) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoWeightedDeparturePencil, nestedCw, sVarw, tVarw,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 5000000 in
/-- Final lower-endpoint channel. -/
theorem coeff_s_sq_t_sq_det_codimensionTwoWeightedDeparturePencil_leftZero_baseOne
    {K : Type*} [CommRing K]
    (D c n C A B : K) :
    (((codimensionTwoWeightedDeparturePencil
      D 1 0 1 c n C A B).det).coeff 2).coeff 2 =
      A^2 * B^2 * (c * n * (D-1)^2 * (c+n-1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoWeightedDeparturePencil, nestedCw, sVarw, tVarw,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 5000000 in
/-- Final upper-endpoint channel. -/
theorem coeff_s_sq_t_sq_det_codimensionTwoWeightedDeparturePencil_leftTop_baseTop
    {K : Type*} [CommRing K]
    (D c n C A B : K) :
    (((codimensionTwoWeightedDeparturePencil
      D (D-1) (D-1) 1 c n C A B).det).coeff 2).coeff 2 =
      A^2 * B^2 *
        (n * (D-1)^2 * (c+1-D) * (c+n-D)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoWeightedDeparturePencil, nestedCw, sVarw, tVarw,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
