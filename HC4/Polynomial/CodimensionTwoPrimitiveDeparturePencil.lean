import HC4.Polynomial.RankThreePencils
import Mathlib.Tactic

/-!
# Codimension-two primitive departure pencil

State-free algebra for the remaining A19.55 same-carrier codimension-two
branch.

For homogeneous exponent vectors

    v = (p, D-p, 0, 0),
    u = (a, D-m-a, m, 0),
    w = (c, D-n-c, 0, n),

write `M(e) = e eᵀ - diag(e)`.  The two-parameter Hessian-core pencil is

    M(v) + s M(u) + t M(w).

We encode `s` as the outer polynomial variable and `t` as the coefficient
polynomial variable.  The coefficient identities below are the exact finite
algebra used by the paper primitive-departure closure.  No valuation state,
Rees clock, or repair transition appears here.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- Base-ring scalar embedded into the nested polynomial ring `K[t][s]`. -/
private def nestedC {K : Type*} [CommRing K]
    (x : K) : Polynomial (Polynomial K) :=
  Polynomial.C (Polynomial.C x)

/-- The outer pencil variable `s`. -/
private def sVar {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.X

/-- The inner pencil variable `t`. -/
private def tVar {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.C Polynomial.X

/-- The codimension-two three-ray Hessian-core pencil. -/
noncomputable def codimensionTwoDeparturePencil
    {K : Type*} [CommRing K]
    (D p a m c n : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  Matrix.of fun i j =>
    nestedC (vectorHessianCore (K := K) ![p, D-p, 0, 0] i j) +
      sVar * nestedC
        (vectorHessianCore (K := K) ![a, D-m-a, m, 0] i j) +
      tVar * nestedC
        (vectorHessianCore (K := K) ![c, D-n-c, 0, n] i j)

set_option maxHeartbeats 4000000 in
/-- The first mixed coefficient is the primitive-departure factor. -/
theorem coeff_s_t_det_codimensionTwoDeparturePencil
    {K : Type*} [CommRing K]
    (D p a m c n : K) :
    (((codimensionTwoDeparturePencil D p a m c n).det).coeff 1).coeff 1 =
      m * n * p * (p - D) * (D - 1) * (m - 1) * (n - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoDeparturePencil, nestedC, sVar, tVar,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
/-- With both departures primitive, the middle extremal channel is the square
`(D-1)^2 (a-c)^2`. -/
theorem coeff_s_sq_t_sq_det_codimensionTwoDeparturePencil_primitive
    {K : Type*} [CommRing K]
    (D p a c : K) :
    (((codimensionTwoDeparturePencil D p a 1 c 1).det).coeff 2).coeff 2 =
      (D - 1)^2 * (a - c)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoDeparturePencil, nestedC, sVar, tVar,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
/-- If the `u` departure is primitive, the `s^3 t` channel forces its active
base exponent to an endpoint. -/
theorem coeff_s_cube_t_det_codimensionTwoDeparturePencil_leftPrimitive
    {K : Type*} [CommRing K]
    (D p a c n : K) :
    (((codimensionTwoDeparturePencil D p a 1 c n).det).coeff 3).coeff 1 =
      a * n * (D - 1) * (n - 1) * (D - a - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoDeparturePencil, nestedC, sVar, tVar,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
/-- In the endpoint case `a=0`, the next `s^2 t` coefficient is exactly the
factor forcing `p=1`. -/
theorem coeff_s_sq_t_det_codimensionTwoDeparturePencil_leftZero
    {K : Type*} [CommRing K]
    (D p c n : K) :
    (((codimensionTwoDeparturePencil D p 0 1 c n).det).coeff 2).coeff 1 =
      -(n * (n - 1) * p * (D - 1)^2 * (p - 1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoDeparturePencil, nestedC, sVar, tVar,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
/-- In the opposite endpoint case `a=D-1`, the same channel factors through
`(p-D)(p-D+1)`. -/
theorem coeff_s_sq_t_det_codimensionTwoDeparturePencil_leftTop
    {K : Type*} [CommRing K]
    (D p c n : K) :
    (((codimensionTwoDeparturePencil D p (D-1) 1 c n).det).coeff 2).coeff 1 =
      -(n * (n - 1) * (D - 1)^2 * (p - D) * (p - D + 1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoDeparturePencil, nestedC, sVar, tVar,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
/-- After `a=0,p=1`, the `s^2 t^2` channel forces the second departure to the
matching endpoint. -/
theorem coeff_s_sq_t_sq_det_codimensionTwoDeparturePencil_leftZero_baseOne
    {K : Type*} [CommRing K]
    (D c n : K) :
    (((codimensionTwoDeparturePencil D 1 0 1 c n).det).coeff 2).coeff 2 =
      c * n * (D - 1)^2 * (c + n - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoDeparturePencil, nestedC, sVar, tVar,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
/-- After `a=D-1,p=D-1`, the corresponding channel factors into the two
possible top endpoints. -/
theorem coeff_s_sq_t_sq_det_codimensionTwoDeparturePencil_leftTop_baseTop
    {K : Type*} [CommRing K]
    (D c n : K) :
    (((codimensionTwoDeparturePencil D (D-1) (D-1) 1 c n).det).coeff 2).coeff 2 =
      n * (D - 1)^2 * (c + 1 - D) * (c + n - D) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoDeparturePencil, nestedC, sVar, tVar,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
