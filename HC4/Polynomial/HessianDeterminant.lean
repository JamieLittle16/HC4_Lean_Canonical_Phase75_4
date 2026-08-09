import HC4.Polynomial.DeterminantWeight

/-!
# Weighted degree of the Hessian determinant

For a weighted-homogeneous potential of degree `d`, the Hessian entry in row
`i`, column `j` has degree `d-wᵢ-wⱼ`.  Every determinant term therefore has
common degree

    card(σ) * d - 2 * Σᵢ wᵢ.

This module proves that statement for actual multivariate polynomial Hessians.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ K : Type*}
variable [Fintype σ] [DecidableEq σ]
variable [CommRing K]

/-- The polynomial determinant of the formal Hessian. -/
noncomputable def hessianDeterminant (p : MvPolynomial σ K) : MvPolynomial σ K :=
  (hessian p).det

/-- The weight of one Leibniz product in the Hessian determinant expansion. -/
def hessianTermWeight (w : σ → ℤ) (d : ℤ) (π : Equiv.Perm σ) : ℤ :=
  ∑ i : σ, (d - w (π i) - w i)

/-- A Hessian determinant term has the sum of the weights of its entries. -/
theorem hessianTerm_isWeightedHomogeneous
    {w : σ → ℤ} {d : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p d)
    (π : Equiv.Perm σ) :
    MvPolynomial.IsWeightedHomogeneous w
      (∏ i : σ, hessian p (π i) i) (hessianTermWeight w d π) := by
  unfold hessianTermWeight
  apply MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i : σ => hessian p (π i) i)
    (fun i : σ => d - w (π i) - w i)
  intro i hi
  exact hessian_entry_isWeightedHomogeneous hp (π i) i

/-- Permuting rows does not change the total Hessian determinant weight. -/
theorem hessianTermWeight_eq (w : σ → ℤ) (d : ℤ) (π : Equiv.Perm σ) :
    hessianTermWeight w d π =
      (Fintype.card σ : ℤ) * d - 2 * ∑ i : σ, w i := by
  have hperm : (∑ i : σ, w (π i)) = ∑ i : σ, w i := by
    simpa using (Equiv.sum_comp π w)
  unfold hessianTermWeight
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hperm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The Hessian determinant of a weighted-homogeneous potential is homogeneous. -/
theorem hessianDeterminant_isWeightedHomogeneous
    {w : σ → ℤ} {d : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p d) :
    MvPolynomial.IsWeightedHomogeneous w (hessianDeterminant p)
      ((Fintype.card σ : ℤ) * d - 2 * ∑ i : σ, w i) := by
  apply determinant_isWeightedHomogeneous
  intro π
  have hterm := hessianTerm_isWeightedHomogeneous hp π
  rw [hessianTermWeight_eq] at hterm
  exact hterm

end

end HC4.Polynomial
