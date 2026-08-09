import HC4.Polynomial.DerivativeWeight
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Weighted-homogeneous determinant expansions

A determinant is a signed sum of permutation products.  If every permutation
product has one common weighted degree, then the determinant itself is
weighted homogeneous of that degree.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {ι σ K : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [CommRing K]

/-- All Leibniz products of a polynomial matrix have the same weighted degree. -/
def DeterminantTermsHomogeneous (w : σ → ℤ)
    (M : Matrix ι ι (MvPolynomial σ K)) (m : ℤ) : Prop :=
  ∀ π : Equiv.Perm ι,
    MvPolynomial.IsWeightedHomogeneous w (∏ i : ι, M (π i) i) m

/-- Common homogeneity of all Leibniz products implies homogeneity of the determinant. -/
theorem determinant_isWeightedHomogeneous
    {w : σ → ℤ} {M : Matrix ι ι (MvPolynomial σ K)} {m : ℤ}
    (hM : DeterminantTermsHomogeneous w M m) :
    MvPolynomial.IsWeightedHomogeneous w M.det m := by
  rw [Matrix.det_apply']
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ
    (fun π : Equiv.Perm ι =>
      (↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
        ∏ i : ι, M (π i) i) m
  intro π hπ
  have hconst : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (↑↑(Equiv.Perm.sign π) : K)) 0 :=
    MvPolynomial.isWeightedHomogeneous_C w (↑↑(Equiv.Perm.sign π) : K)
  have hprod : MvPolynomial.IsWeightedHomogeneous w
      ((MvPolynomial.C (↑↑(Equiv.Perm.sign π) : K)) *
        ∏ i : ι, M (π i) i) (0 + m) :=
    MvPolynomial.IsWeightedHomogeneous.mul hconst (hM π)
  simpa using hprod

/-- The determinant lies entirely in its common exact weighted component. -/
theorem initialForm_determinant_eq_self
    {w : σ → ℤ} {M : Matrix ι ι (MvPolynomial σ K)} {m : ℤ}
    (hM : DeterminantTermsHomogeneous w M m) :
    initialForm w m M.det = M.det := by
  exact initialForm_eq_self_of_isWeightedHomogeneous
    (determinant_isWeightedHomogeneous hM)

end

end HC4.Polynomial
