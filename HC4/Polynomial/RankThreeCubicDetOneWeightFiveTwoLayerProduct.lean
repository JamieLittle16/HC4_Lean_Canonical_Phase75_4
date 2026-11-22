import HC4.Polynomial.RankThreeCubicDetOneFirstVariationCoefficient
import HC4.Polynomial.RankThreeCubicDetOneWeightFiveSourceGap
import Mathlib.Tactic

/-!
# First-lower weighted component of two adjacent homogeneous layers

For homogeneous A,C with weights m,n and B,D with weights
m-1,n-1, the exact weight-(m+n-1) component of
(A+B)(C+D) consists of precisely A*D+B*C.

This elementary source-honest weighted first-variation identity is
the local multiplication step of the weight-five Hessian determinant
calculation. It neither assumes det(A) is invertible nor asserts
a new pole obstruction.
-/

namespace HC4.Polynomial

open MvPolynomial
noncomputable section

variable {σ K : Type*} [CommRing K]

/-- An exact weight-one-lower projection of a product of two
adjacent-layer polynomials contains exactly one lower factor. -/
theorem initialForm_mul_two_adjacent_layers
    (w : σ → ℤ) (m n : ℤ)
    (A B C D : MvPolynomial σ K)
    (hA : MvPolynomial.IsWeightedHomogeneous w A m)
    (hB : MvPolynomial.IsWeightedHomogeneous w B (m - 1))
    (hC : MvPolynomial.IsWeightedHomogeneous w C n)
    (hD : MvPolynomial.IsWeightedHomogeneous w D (n - 1)) :
    initialForm w (m + n - 1) ((A + B) * (C + D)) =
      A * D + B * C := by
  have hAC : MvPolynomial.IsWeightedHomogeneous w (A * C)
      (m + n) := hA.mul hC
  have hAD : MvPolynomial.IsWeightedHomogeneous w (A * D)
      (m + n - 1) := by
    have h := hA.mul hD
    have heq : m + (n - 1) = m + n - 1 := by omega
    rw [heq] at h
    exact h
  have hBC : MvPolynomial.IsWeightedHomogeneous w (B * C)
      (m + n - 1) := by
    have h := hB.mul hC
    have heq : (m - 1) + n = m + n - 1 := by omega
    rw [heq] at h
    exact h
  have hBD : MvPolynomial.IsWeightedHomogeneous w (B * D)
      (m + n - 2) := by
    have h := hB.mul hD
    have heq : (m - 1) + (n - 1) = m + n - 2 := by omega
    rw [heq] at h
    exact h
  have hfirst :
      MvPolynomial.IsWeightedHomogeneous w (A * D + B * C)
        (m + n - 1) := hAD.add hBC
  have htop_zero :
      initialForm w (m + n - 1) (A * C) = 0 :=
    initialForm_eq_zero_of_isWeightedHomogeneous hAC (m + n - 1)
      (by omega)
  have hbottom_zero :
      initialForm w (m + n - 1) (B * D) = 0 :=
    initialForm_eq_zero_of_isWeightedHomogeneous hBD (m + n - 1)
      (by omega)
  calc
    initialForm w (m + n - 1) ((A + B) * (C + D)) =
        initialForm w (m + n - 1)
          (A * C + (A * D + B * C) + B * D) := by
          congr 1
          ring
    _ = initialForm w (m + n - 1) (A * C) +
          initialForm w (m + n - 1) (A * D + B * C) +
          initialForm w (m + n - 1) (B * D) := by
          rw [initialForm_add, initialForm_add]
    _ = A * D + B * C := by
          rw [htop_zero, hbottom_zero,
            initialForm_eq_self_of_isWeightedHomogeneous hfirst]
          simp

end
end HC4.Polynomial
