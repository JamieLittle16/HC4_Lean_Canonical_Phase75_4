import Mathlib.Tactic

/-!
# Cubic Hessian with identically zero tangential binary block

A ternary cubic that restricts to zero on the plane z=0
has the homogeneous form
  f(z,u,v) = α*z³ + z²*(β*u+γ*v)
             + z*(m*u²+2*n*u*v+l*v²),
up to an inessential common Hessian factor.

Its rescaled symmetric cubic Hessian pencil is the explicit
matrix below. Its determinant is

  -Δ*z*(m*u²+2*n*u*v+l*v²)
  -Δ*z²*(β*u+γ*v)
  +z³*(α*Δ-β²*l+2*β*γ*n-γ²*m),

where Δ=m*l-n².

In particular, if Δ=0 then the determinant is a scalar times
z³, not merely divisible by z². This is the candidate
finite coefficient obstruction to a genuinely exactly-double
source pole with zero binary tangent Hessian.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix

noncomputable section

/-- The general symmetric ternary cubic Hessian with zero
binary tangent block at z=0, normalized as a linear pencil. -/
def cubicZeroBinaryHessian
    {R : Type*} [CommRing R]
    (alpha beta gamma m n l z u v : R) :
    Matrix (Fin 3) (Fin 3) R :=
  ![![alpha * z + beta * u + gamma * v,
      beta * z + m * u + n * v,
      gamma * z + n * u + l * v],
    ![beta * z + m * u + n * v, m * z, n * z],
    ![gamma * z + n * u + l * v, n * z, l * z]]

/-- Exact finite determinant expansion. Both the coefficient
of z and the coefficient of z² contain Δ=m*l-n². -/
theorem cubicZeroBinaryHessian_det_expansion
    {R : Type*} [CommRing R]
    (alpha beta gamma m n l z u v : R) :
    (cubicZeroBinaryHessian alpha beta gamma m n l z u v).det =
      -(m * l - n ^ 2) * z *
        (m * u ^ 2 + 2 * n * u * v + l * v ^ 2) -
      (m * l - n ^ 2) * z ^ 2 * (beta * u + gamma * v) +
      z ^ 3 * (alpha * (m * l - n ^ 2) -
        beta ^ 2 * l + 2 * beta * gamma * n - gamma ^ 2 * m) := by
  simp [cubicZeroBinaryHessian, Matrix.det_fin_three]
  ring

/-- Vanishing discriminant upgrades the zero-binary-plane Hessian
determinant to an exact cubic power of the normal coordinate. -/
theorem cubicZeroBinaryHessian_det_triple_of_discriminant_zero
    {R : Type*} [CommRing R]
    (alpha beta gamma m n l z u v : R)
    (hdisc : m * l = n ^ 2) :
    (cubicZeroBinaryHessian alpha beta gamma m n l z u v).det =
      z ^ 3 *
        (-beta ^ 2 * l + 2 * beta * gamma * n -
          gamma ^ 2 * m) := by
  rw [cubicZeroBinaryHessian_det_expansion]
  rw [sub_eq_zero.mpr hdisc]
  ring


/-- Over a characteristic-zero field, if the determinant of a
zero-binary-block cubic Hessian has a square normal factor
with an affine-linear quotient, then the binary quadratic
discriminant vanishes. In particular its determinant has a
*cubic* normal factor by the preceding theorem.

This is the finite coefficient obstruction; the source-specific
step must still transport its original factorisation into
the adapted coordinates. -/
theorem cubicZeroBinaryHessian_discriminant_zero_of_squareNormalFactor
    {K : Type*} [Field K] [CharZero K]
    (alpha beta gamma m n l A B C : K)
    (hfactor : ∀ z u v : K,
      (cubicZeroBinaryHessian alpha beta gamma m n l z u v).det =
        z ^ 2 * (A * z + B * u + C * v)) :
    m * l = n ^ 2 := by
  have hlin (u v : K) :
      (m * l - n ^ 2) *
        (m * u ^ 2 + 2 * n * u * v + l * v ^ 2) = 0 := by
    have h1 := hfactor 1 u v
    have hm1 := hfactor (-1) u v
    have h2 := hfactor 2 u v
    rw [cubicZeroBinaryHessian_det_expansion] at h1 hm1 h2
    norm_num at h1 hm1 h2
    have h6 :
        (6 : K) * ((m * l - n ^ 2) *
          (m * u ^ 2 + 2 * n * u * v + l * v ^ 2)) = 0 := by
      linear_combination -(6 * h1 - 2 * hm1 - h2)
    exact (mul_eq_zero.mp h6).resolve_left (by norm_num)
  have hm : (m * l - n ^ 2) * m = 0 := by
    simpa using hlin 1 0
  have hl : (m * l - n ^ 2) * l = 0 := by
    simpa using hlin 0 1
  have hn : (m * l - n ^ 2) * (m + 2 * n + l) = 0 := by
    convert hlin 1 1 using 1 <;> ring
  by_cases hd : m * l - n ^ 2 = 0
  · exact sub_eq_zero.mp hd
  · have hm0 : m = 0 := (mul_eq_zero.mp hm).resolve_left hd
    have hl0 : l = 0 := (mul_eq_zero.mp hl).resolve_left hd
    have hn0 : n = 0 := by
      have h2n : (m * l - n ^ 2) * (2 * n) = 0 := by
        simpa [hm0, hl0] using hn
      have h : (2 : K) * n = 0 :=
        (mul_eq_zero.mp h2n).resolve_left hd
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    exact False.elim (hd (by simp [hm0, hl0, hn0]))

end
end HC4.Polynomial.RankThreeCubic
