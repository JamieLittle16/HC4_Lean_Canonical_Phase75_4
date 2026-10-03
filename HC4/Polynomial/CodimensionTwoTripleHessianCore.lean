import HC4.Polynomial.RankThreePencils
import Mathlib.Tactic

/-!
# Codimension-two three-ray Hessian core

This file isolates the finite determinant calculation used by the A19.55
same-carrier codimension-two primitive-departure argument.

For homogeneous exponent vectors

    v = (p, D-p, 0, 0),
    u = (a, D-m-a, m, 0),
    w = (c, D-n-c, 0, n),

write `M(e) = e eᵀ - diag(e)`.  The Hessian of a homogeneous monomial is a
monomial factor times `M(e)`, so the projective three-term Hessian core is

    M(v) + s M(u) + t M(w).

Its determinant has only the six mixed monomials

    s t, s² t, s t², s³ t, s² t², s t³.

The first coefficient is the primitive-departure factor

    -m n p (D-p) (D-1) (m-1) (n-1).

Keeping this calculation state-free prevents symbolic determinant expansion
from being repeated against the large A19 terminal records.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- The projective Hessian core of a codimension-two vertex together with one
departure in each missing coordinate. -/
def codimensionTwoTripleHessianCore
    {K : Type*} [CommRing K]
    (D p a c m n s t : K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j =>
    vectorHessianCore (K := K) ![p, D - p, 0, 0] i j +
      s * vectorHessianCore (K := K) ![a, D - m - a, m, 0] i j +
      t * vectorHessianCore (K := K) ![c, D - n - c, 0, n] i j

set_option maxHeartbeats 4000000 in
/-- **Exact six-term determinant expansion.**

No support or positivity hypotheses enter this identity; it is a fixed
`4 x 4` calculation over an arbitrary commutative ring. -/
theorem det_codimensionTwoTripleHessianCore
    {K : Type*} [CommRing K]
    (D p a c m n s t : K) :
    (codimensionTwoTripleHessianCore D p a c m n s t).det =
      s * t *
          (m * n * p * (-D + p) * (D - 1) * (m - 1) * (n - 1)) +
      s ^ 2 * t *
          (m * n * (D - 1) * (n - 1) *
            (-D * a ^ 2 - D * a * m + 2 * D * a * p + D * a -
              D * p ^ 2 + D * p - 2 * a * p + m * p ^ 2 - m * p)) +
      s * t ^ 2 *
          (m * n * (D - 1) * (m - 1) *
            (-D * c ^ 2 - D * c * n + 2 * D * c * p + D * c -
              D * p ^ 2 + D * p - 2 * c * p + n * p ^ 2 - n * p)) +
      s ^ 3 * t *
          (-a * m * n * (D - 1) * (n - 1) * (-D + a + m)) +
      s ^ 2 * t ^ 2 *
          (-m * n * (D - 1) *
            (-D * a ^ 2 + 2 * D * a * c - D * a * m + D * a -
              D * c ^ 2 - D * c * n + D * c + a ^ 2 * n - 2 * a * c +
              a * m * n - a * n + c ^ 2 * m + c * m * n - c * m)) +
      s * t ^ 3 *
          (-c * m * n * (D - 1) * (m - 1) * (-D + c + n)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoTripleHessianCore, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove, pow_two]
  ring

/-- The first mixed coefficient, written in the sign convention used by the
A19 paper argument. -/
theorem codimensionTwoTriple_firstMixedFactor
    {K : Type*} [CommRing K]
    (D p m n : K) :
    m * n * p * (-D + p) * (D - 1) * (m - 1) * (n - 1) =
      -(m * n * p * (D - p) * (D - 1) * (m - 1) * (n - 1)) := by
  ring

/-- If both departures are primitive (`m=n=1`), the sole surviving quartic
mixed coefficient is the square `(D-1)^2 (a-c)^2`. -/
theorem codimensionTwoTriple_bothPrimitive_middleFactor
    {K : Type*} [CommRing K]
    (D a c : K) :
    -(1 : K) * 1 * (D - 1) *
        (-D * a ^ 2 + 2 * D * a * c - D * a + D * a -
          D * c ^ 2 - D * c + D * c + a ^ 2 - 2 * a * c +
          a - a + c ^ 2 + c - c) =
      (D - 1) ^ 2 * (a - c) ^ 2 := by
  ring

/-- In the asymmetric branch `m=1<n`, the `s^3 t` channel factors into the
endpoint factor used to force `a=0` or `a=D-1`. -/
theorem codimensionTwoTriple_m_one_cubicFactor
    {K : Type*} [CommRing K]
    (D a n : K) :
    -a * 1 * n * (D - 1) * (n - 1) * (-D + a + 1) =
      -a * n * (D - 1) * (n - 1) * (a - (D - 1)) := by
  ring

/-- With `m=1` and `a=0`, the `s^2 t` channel is the factor forcing `p=1`
under the nondegeneracy hypotheses of the A19 carrier. -/
theorem codimensionTwoTriple_m_one_a_zero_quadraticFactor
    {K : Type*} [CommRing K]
    (D p n : K) :
    1 * n * (D - 1) * (n - 1) *
        (-D * 0 ^ 2 - D * 0 * 1 + 2 * D * 0 * p + D * 0 -
          D * p ^ 2 + D * p - 2 * 0 * p + 1 * p ^ 2 - 1 * p) =
      -n * p * (D - 1) ^ 2 * (n - 1) * (p - 1) := by
  ring

/-- With `m=1`, `a=0`, the middle channel factors into the final `c`-equation. -/
theorem codimensionTwoTriple_m_one_a_zero_middleFactor
    {K : Type*} [CommRing K]
    (D c n : K) :
    -1 * n * (D - 1) *
        (-D * 0 ^ 2 + 2 * D * 0 * c - D * 0 * 1 + D * 0 -
          D * c ^ 2 - D * c * n + D * c + 0 ^ 2 * n - 2 * 0 * c +
          0 * 1 * n - 0 * n + c ^ 2 * 1 + c * 1 * n - c * 1) =
      c * n * (D - 1) ^ 2 * (c + n - 1) := by
  ring

/-- The symmetric high-active endpoint `a=D-1` gives the companion `p`
factor. -/
theorem codimensionTwoTriple_m_one_a_top_quadraticFactor
    {K : Type*} [CommRing K]
    (D p n : K) :
    1 * n * (D - 1) * (n - 1) *
        (-D * (D - 1) ^ 2 - D * (D - 1) * 1 +
          2 * D * (D - 1) * p + D * (D - 1) - D * p ^ 2 + D * p -
          2 * (D - 1) * p + 1 * p ^ 2 - 1 * p) =
      -n * (-D + p) * (D - 1) ^ 2 * (n - 1) * (-D + p + 1) := by
  ring

/-- And the middle channel factors into the two possible `c` endpoints. -/
theorem codimensionTwoTriple_m_one_a_top_middleFactor
    {K : Type*} [CommRing K]
    (D c n : K) :
    -1 * n * (D - 1) *
        (-D * (D - 1) ^ 2 + 2 * D * (D - 1) * c -
          D * (D - 1) * 1 + D * (D - 1) - D * c ^ 2 -
          D * c * n + D * c + (D - 1) ^ 2 * n -
          2 * (D - 1) * c + (D - 1) * 1 * n -
          (D - 1) * n + c ^ 2 * 1 + c * 1 * n - c * 1) =
      n * (D - 1) ^ 2 * (-D + c + 1) * (-D + c + n) := by
  ring

end

end HC4.Polynomial
