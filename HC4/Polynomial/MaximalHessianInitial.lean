import HC4.Polynomial.TopProduct
import HC4.Polynomial.HessianDeterminant

/-!
# Hessian determinant of a maximal weighted initial form

This is the algebraic core of the manuscript's Hessian initial-form lemma.
If `p` has no monomials above weight `m` and `H` is its exact weight-`m`
component, then the determinant component at

    card(σ) * m - 2 * Σ_i w_i

is exactly `det Hess H`.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ K : Type*}
variable [Fintype σ] [DecidableEq σ]
variable [CommRing K]

/-- The Hessian determinant component at the maximal possible weight is the
Hessian determinant of the maximal initial form. -/
theorem initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
    (w : σ → ℤ) (m : ℤ) (p : MvPolynomial σ K)
    (hp : IsWeightLE w m p) :
    initialForm w ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
        (hessianDeterminant p) =
      hessianDeterminant (initialForm w m p) := by
  classical
  let H : MvPolynomial σ K := initialForm w m p
  let R : MvPolynomial σ K := p - H
  have hHhom : MvPolynomial.IsWeightedHomogeneous w H m := by
    exact initialForm_isWeightedHomogeneous w m p
  have hRlt : IsWeightLT w m R := by
    exact sub_initialForm_isWeightLT hp
  have hpH : p = H + R := by
    dsimp [R]
    ring
  have hentryDiff : ∀ i j : σ,
      IsWeightLT w (m - w i - w j)
        (hessian p i j - hessian H i j) := by
    intro i j
    have heq : hessian p i j - hessian H i j = hessian R i j := by
      rw [hpH]
      simp [hessian_apply]
    rw [heq]
    exact hRlt.hessian_entry i j
  -- Expand both determinants.  `rw [Matrix.det_apply']` rewrites one
  -- occurrence at a time in this pinned Lean/Mathlib version, so invoke it
  -- once for the determinant under `initialForm` and once for the RHS.
  rw [hessianDeterminant, hessianDeterminant,
    Matrix.det_apply', Matrix.det_apply']
  -- We use the determinant Leibniz expansion term by term.  All terms have
  -- the same top weight, and each top term is obtained by using only `H`.
  change initialForm w ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
      (∑ π : Equiv.Perm σ,
        (↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
          ∏ i : σ, hessian p (π i) i) =
    ∑ π : Equiv.Perm σ,
      (↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
        ∏ i : σ, hessian H (π i) i
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  have hprod :
      initialForm w ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
          (∏ i : σ, hessian p (π i) i) =
        ∏ i : σ, hessian H (π i) i := by
    have hweights :
        (∑ i : σ, (m - w (π i) - w i)) =
          (Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i :=
      hessianTermWeight_eq w m π
    rw [← hweights]
    apply initialForm_prod_eq_prod Finset.univ w
      (fun i : σ => m - w (π i) - w i)
      (fun i : σ => hessian p (π i) i)
      (fun i : σ => hessian H (π i) i)
    · intro i hi
      exact hessian_entry_isWeightedHomogeneous hHhom (π i) i
    · intro i hi
      exact hentryDiff (π i) i
  let c : K := ↑↑(Equiv.Perm.sign π)
  change initialForm w ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
      (MvPolynomial.C c * ∏ i : σ, hessian p (π i) i) =
    MvPolynomial.C c * ∏ i : σ, hessian H (π i) i
  calc
    initialForm w ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
        (MvPolynomial.C c * ∏ i : σ, hessian p (π i) i)
        = initialForm w ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
            (c • (∏ i : σ, hessian p (π i) i)) := by
              rw [MvPolynomial.C_mul']
    _ = c • initialForm w ((Fintype.card σ : ℤ) * m - 2 * ∑ i : σ, w i)
          (∏ i : σ, hessian p (π i) i) := by
            rw [initialForm_smul]
    _ = c • (∏ i : σ, hessian H (π i) i) := by rw [hprod]
    _ = MvPolynomial.C c * ∏ i : σ, hessian H (π i) i := by
          rw [MvPolynomial.C_mul']

/-- A zero Hessian determinant remains zero on every maximal weighted initial form. -/
theorem hessianDeterminant_initialForm_eq_zero_of_eq_zero
    (w : σ → ℤ) (m : ℤ) (p : MvPolynomial σ K)
    (hp : IsWeightLE w m p)
    (hzero : hessianDeterminant p = 0) :
    hessianDeterminant (initialForm w m p) = 0 := by
  rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m p hp]
  rw [hzero, initialForm_zero]

end

end HC4.Polynomial
