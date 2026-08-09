import HC4.Polynomial.WeightedInitial
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Weighted initial forms and formal partial differentiation

Formal differentiation lowers integer weight by the weight of the variable.
The exact weighted-component projector therefore commutes with partial
 differentiation after shifting the selected weight.  The same statement is
recorded entrywise for the polynomial Hessian.
-/

namespace HC4.Polynomial

open MvPolynomial

noncomputable section

variable {σ K : Type*} [CommSemiring K]

/-- Partial differentiation lowers weighted degree by the variable weight. -/
theorem pderiv_isWeightedHomogeneous
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p m) (i : σ) :
    MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.pderiv i p) (m - w i) := by
  exact hp.pderiv (by abel)

/-- Exact weighted components commute with a formal partial derivative.

The proof deliberately avoids any coefficient-level formula for `pderiv`.
Instead it inducts over the monomial decomposition.  A monomial lies in one
exact weight component, and its derivative is weighted homogeneous in the
correspondingly shifted degree.  This makes the statement stable across
Mathlib versions where the coefficient API for `pderiv` has changed.
-/
theorem pderiv_initialForm (w : σ → ℤ) (m : ℤ)
    (p : MvPolynomial σ K) (i : σ) :
    MvPolynomial.pderiv i (initialForm w m p) =
      initialForm w (m - w i) (MvPolynomial.pderiv i p) := by
  classical
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro u a
    let mu : ℤ := Finsupp.weight w u
    have hmono :
        MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.monomial u a) mu := by
      exact MvPolynomial.isWeightedHomogeneous_monomial w u a rfl
    by_cases h : mu = m
    · have hm :
          MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.monomial u a) m := by
        simpa [h] using hmono
      rw [initialForm_eq_self_of_isWeightedHomogeneous hm]
      rw [initialForm_eq_self_of_isWeightedHomogeneous
        (pderiv_isWeightedHomogeneous hm i)]
    · have hleft : initialForm w m (MvPolynomial.monomial u a) = 0 := by
        exact initialForm_eq_zero_of_isWeightedHomogeneous hmono m (Ne.symm h)
      have hderiv := pderiv_isWeightedHomogeneous hmono i
      have hshift : m - w i ≠ mu - w i := by
        intro hs
        apply h
        calc
          mu = (mu - w i) + w i := by abel
          _ = (m - w i) + w i := by rw [← hs]
          _ = m := by abel
      have hright :
          initialForm w (m - w i) (MvPolynomial.pderiv i (MvPolynomial.monomial u a)) = 0 := by
        exact initialForm_eq_zero_of_isWeightedHomogeneous hderiv (m - w i) hshift
      rw [hleft, map_zero, hright]
  · intro p q hp hq
    simp only [map_add]
    rw [hp, hq]

/-- The formal Hessian matrix of a multivariate polynomial. -/
noncomputable def hessian (p : MvPolynomial σ K) :
    Matrix σ σ (MvPolynomial σ K) :=
  Matrix.of fun i j => MvPolynomial.pderiv j (MvPolynomial.pderiv i p)

@[simp]
theorem hessian_apply (p : MvPolynomial σ K) (i j : σ) :
    hessian p i j = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := rfl

/-- Every Hessian entry of a weighted-homogeneous polynomial has the expected weight. -/
theorem hessian_entry_isWeightedHomogeneous
    {w : σ → ℤ} {m : ℤ} {p : MvPolynomial σ K}
    (hp : MvPolynomial.IsWeightedHomogeneous w p m) (i j : σ) :
    MvPolynomial.IsWeightedHomogeneous w (hessian p i j)
      (m - w i - w j) := by
  exact pderiv_isWeightedHomogeneous
    (pderiv_isWeightedHomogeneous hp i) j

/-- Hessian formation commutes entrywise with exact initial forms. -/
theorem hessian_initialForm_entry (w : σ → ℤ) (m : ℤ)
    (p : MvPolynomial σ K) (i j : σ) :
    hessian (initialForm w m p) i j =
      initialForm w (m - w i - w j) (hessian p i j) := by
  simp only [hessian_apply]
  rw [pderiv_initialForm, pderiv_initialForm]

end

end HC4.Polynomial
