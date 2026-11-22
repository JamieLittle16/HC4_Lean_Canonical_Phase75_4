import HC4.Polynomial.RankThreeCubicDetOneWeightFiveTwoLayerProduct
import Mathlib.Tactic

/-!
# First lower component of an arbitrary bounded product

Unlike the adjacent-homogeneous-layer identity, this result permits
arbitrary lower terms. If p and q are bounded above by m and n,
respectively, then their component at weight m+n-1 is the sum of
the two cross products of their top and next components.

The proof removes the exact top two components of each input,
then uses a strict one-extra-weight gap to eliminate the remainders.
This is the reusable two-factor inductive step for the four-factor
Hessian determinant Leibniz products.
-/

namespace HC4.Polynomial

open MvPolynomial
noncomputable section

variable {σ K : Type*} [CommRing K] [DecidableEq σ]

/-- Remove the actual top and next weighted components of a
bounded polynomial. Its remaining support is strictly lower. -/
theorem sub_two_initialForms_isWeightLT
    (w : σ → ℤ) (m : ℤ) (p : MvPolynomial σ K)
    (hp : IsWeightLE w m p) :
    IsWeightLT w (m - 1)
      ((p - initialForm w m p) - initialForm w (m - 1) p) := by
  have htop : IsWeightLT w m (p - initialForm w m p) :=
    sub_initialForm_isWeightLT hp
  have hnextBound :
      IsWeightLE w (m - 1) (p - initialForm w m p) := by
    intro d hd
    have h := htop hd
    omega
  have htopGone :
      initialForm w (m - 1) (initialForm w m p) = 0 := by
    exact initialForm_eq_zero_of_isWeightedHomogeneous
      (initialForm_isWeightedHomogeneous w m p)
      (m - 1) (by omega)
  have hnext :
      initialForm w (m - 1) (p - initialForm w m p) =
        initialForm w (m - 1) p := by
    rw [map_sub, htopGone, sub_zero]
  have h := sub_initialForm_isWeightLT hnextBound
  rw [hnext] at h
  exact h

/-- The first lower component of a product of two weakly-bounded
polynomials is the first variation of the top component. -/
theorem initialForm_mul_first_lower
    (w : σ → ℤ) (m n : ℤ)
    (p q : MvPolynomial σ K)
    (hp : IsWeightLE w m p)
    (hq : IsWeightLE w n q) :
    initialForm w (m + n - 1) (p * q) =
      initialForm w m p * initialForm w (n - 1) q +
      initialForm w (m - 1) p * initialForm w n q := by
  let A := initialForm w m p
  let B := initialForm w (m - 1) p
  let C := initialForm w n q
  let D := initialForm w (n - 1) q
  have hA : MvPolynomial.IsWeightedHomogeneous w A m :=
    initialForm_isWeightedHomogeneous w m p
  have hB : MvPolynomial.IsWeightedHomogeneous w B (m - 1) :=
    initialForm_isWeightedHomogeneous w (m - 1) p
  have hC : MvPolynomial.IsWeightedHomogeneous w C n :=
    initialForm_isWeightedHomogeneous w n q
  have hD : MvPolynomial.IsWeightedHomogeneous w D (n - 1) :=
    initialForm_isWeightedHomogeneous w (n - 1) q
  have hAp : IsWeightLE w m (A + B) := by
    have hAw := isWeightLE_of_isWeightedHomogeneous hA
    have hBw : IsWeightLE w m B := by
      intro d hd
      have h := (isWeightLE_of_isWeightedHomogeneous hB) hd
      omega
    exact hAw.add hBw
  have hCq : IsWeightLE w n (C + D) := by
    have hCw := isWeightLE_of_isWeightedHomogeneous hC
    have hDw : IsWeightLE w n D := by
      intro d hd
      have h := (isWeightLE_of_isWeightedHomogeneous hD) hd
      omega
    exact hCw.add hDw
  have hRp : IsWeightLT w (m - 1) (p - (A + B)) := by
    have h := sub_two_initialForms_isWeightLT w m p hp
    convert h using 1 <;> ring
  have hRq : IsWeightLT w (n - 1) (q - (C + D)) := by
    have h := sub_two_initialForms_isWeightLT w n q hq
    convert h using 1 <;> ring
  have h1 : IsWeightLT w (m + n - 1)
      ((p - (A + B)) * q) := by
    convert hRp.mul_le hq using 1 <;> omega
  have h2 : IsWeightLT w (m + n - 1)
      ((A + B) * (q - (C + D))) := by
    convert hAp.mul_lt hRq using 1 <;> omega
  have hdiff : IsWeightLT w (m + n - 1)
      (p * q - (A + B) * (C + D)) := by
    have h := h1.add h2
    convert h using 1 <;> ring
  have hz := initialForm_eq_zero_of_isWeightLT hdiff (le_refl _)
  rw [map_sub] at hz
  have heq := sub_eq_zero.mp hz
  calc
    initialForm w (m + n - 1) (p * q) =
        initialForm w (m + n - 1) ((A + B) * (C + D)) := heq
    _ = A * D + B * C :=
      initialForm_mul_two_adjacent_layers w m n A B C D hA hB hC hD

end
end HC4.Polynomial
