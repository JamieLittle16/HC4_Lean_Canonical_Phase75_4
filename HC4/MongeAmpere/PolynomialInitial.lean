import HC4.Polynomial.HessianDeterminant

/-!
# Weighted consequences of the polynomial Monge--Ampère equation

If a polynomial Hessian determinant is equal to `1`, every nonzero exact
weighted component of that determinant vanishes.  For a weighted-homogeneous
potential, the common Hessian-determinant degree must therefore be zero.
-/

namespace HC4.MongeAmpere

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ K : Type*}
variable [Fintype σ] [DecidableEq σ]
variable [CommRing K] [Nontrivial K]

/-- The polynomial Monge--Ampère condition. -/
def IsPolynomialMongeAmpere (p : MvPolynomial σ K) : Prop :=
  HC4.Polynomial.hessianDeterminant p = 1

/-- Every nonzero weighted component of a determinant-one Hessian vanishes. -/
theorem initialForm_hessianDeterminant_eq_zero
    {w : σ → ℤ} {c : ℤ} {p : MvPolynomial σ K}
    (hMA : IsPolynomialMongeAmpere p) (hc : c ≠ 0) :
    HC4.Polynomial.initialForm w c
      (HC4.Polynomial.hessianDeterminant p) = 0 := by
  change HC4.Polynomial.hessianDeterminant p = 1 at hMA
  rw [hMA]
  exact HC4.Polynomial.initialForm_eq_zero_of_isWeightedHomogeneous
    (MvPolynomial.isWeightedHomogeneous_one K w) c hc

/-- A homogeneous determinant-one Hessian can only have determinant weight zero. -/
theorem hessianDeterminant_weight_eq_zero
    {w : σ → ℤ} {d : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p d)
    (hMA : IsPolynomialMongeAmpere p) :
    (Fintype.card σ : ℤ) * d - 2 * ∑ i : σ, w i = 0 := by
  change HC4.Polynomial.hessianDeterminant p = 1 at hMA
  have hhom := HC4.Polynomial.hessianDeterminant_isWeightedHomogeneous hp
  have hne : HC4.Polynomial.hessianDeterminant p ≠ 0 := by
    rw [hMA]
    exact one_ne_zero
  have hone : MvPolynomial.IsWeightedHomogeneous w
      (HC4.Polynomial.hessianDeterminant p) 0 := by
    rw [hMA]
    exact MvPolynomial.isWeightedHomogeneous_one K w
  exact MvPolynomial.IsWeightedHomogeneous.inj_right hne hhom hone

/-- A strictly positive predicted Hessian-determinant weight contradicts determinant one. -/
theorem not_isPolynomialMongeAmpere_of_positive_hessian_weight
    {w : σ → ℤ} {d : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p d)
    (hpos : 0 < (Fintype.card σ : ℤ) * d - 2 * ∑ i : σ, w i) :
    ¬ IsPolynomialMongeAmpere p := by
  intro hMA
  have hz := hessianDeterminant_weight_eq_zero hp hMA
  linarith

end

end HC4.MongeAmpere
