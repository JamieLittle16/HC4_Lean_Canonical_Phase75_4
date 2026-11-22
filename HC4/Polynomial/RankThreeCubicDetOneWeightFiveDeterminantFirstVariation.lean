import HC4.Polynomial.RankThreeCubicDetOneWeightFiveFiniteProduct
import HC4.Polynomial.RankThreeCubicDetOneFirstVariationColumns
import Mathlib.Tactic

/-!
# Determinant first-lower weighted component is its adjugate first variation

For a square polynomial matrix M with entry weights b(i,j) whose
permutation sums all equal d, its weight-(d-1) determinant component
is exactly the sum of one-column replacements of its top-entry
matrix A by the next-entry matrix B.

This statement is source-neutral and valid for singular A.
It combines the FINITE-PRODUCT weighted coefficient theorem
with the Leibniz determinant expansion, followed by the already
verified cofactor/adjugate first-variation identity.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {σ K ι : Type*}
variable [CommRing K] [DecidableEq σ] [Fintype ι] [DecidableEq ι]

/-- The first lower determinant component is the sum of
one-column replacements by the next-weight matrix entries. -/
theorem initialForm_det_first_lower_eq_updateCols
    (w : σ → ℤ) (d : ℤ) (b : ι → ι → ℤ)
    (M A B : Matrix ι ι (MvPolynomial σ K))
    (hweights : ∀ π : Equiv.Perm ι, (∑ j : ι, b (π j) j) = d)
    (hM : ∀ i j : ι, IsWeightLE w (b i j) (M i j))
    (hA : ∀ i j : ι, A i j = initialForm w (b i j) (M i j))
    (hB : ∀ i j : ι, B i j = initialForm w (b i j - 1) (M i j)) :
    initialForm w (d - 1) M.det =
      ∑ j : ι, (A.updateCol j (fun i => B i j)).det := by
  classical
  have hterm (π : Equiv.Perm ι) :
      initialForm w (d - 1) (∏ j : ι, M (π j) j) =
        ∑ j : ι, B (π j) j *
          ∏ k ∈ Finset.univ.erase j, A (π k) k := by
    have ht := initialForm_prod_first_lower
      (Finset.univ : Finset ι) w
      (fun j : ι => b (π j) j)
      (fun j : ι => M (π j) j)
      (fun j _ => hM (π j) j)
    rw [hweights π] at ht
    simpa only [← hA, ← hB] using ht
  have hsigned (π : Equiv.Perm ι) :
      initialForm w (d - 1)
        ((↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
          ∏ j : ι, M (π j) j) =
        (↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
          (∑ j : ι, B (π j) j *
            ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
    let c : K := ↑↑(Equiv.Perm.sign π)
    change initialForm w (d - 1)
        (MvPolynomial.C c * ∏ j : ι, M (π j) j) =
      MvPolynomial.C c *
        (∑ j : ι, B (π j) j *
          ∏ k ∈ Finset.univ.erase j, A (π k) k)
    calc
      initialForm w (d - 1)
          (MvPolynomial.C c * ∏ j : ι, M (π j) j) =
        initialForm w (d - 1)
          (c • (∏ j : ι, M (π j) j)) := by
            rw [MvPolynomial.C_mul']
      _ = c • initialForm w (d - 1)
            (∏ j : ι, M (π j) j) := by
            rw [initialForm_smul]
      _ = c • (∑ j : ι, B (π j) j *
            ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
            rw [hterm π]
      _ = MvPolynomial.C c *
            (∑ j : ι, B (π j) j *
              ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
            rw [MvPolynomial.C_mul']
  rw [Matrix.det_apply', map_sum]
  calc
    (∑ π : Equiv.Perm ι,
        initialForm w (d - 1)
          ((↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
            ∏ j : ι, M (π j) j)) =
      ∑ π : Equiv.Perm ι,
        (↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
          (∑ j : ι, B (π j) j *
            ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
          apply Finset.sum_congr rfl
          intro π _
          exact hsigned π
    _ = ∑ j : ι, ∑ π : Equiv.Perm ι,
        (↑↑(Equiv.Perm.sign π) : MvPolynomial σ K) *
          (B (π j) j *
            ∏ k ∈ Finset.univ.erase j, A (π k) k) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ j : ι, (A.updateCol j (fun i => B i j)).det := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Matrix.det_apply']
          apply Finset.sum_congr rfl
          intro π _
          rw [updateCol_perm_product_eq_single_linear_term A B π j]

/-- The first lower determinant component is the adjugate
first-variation pairing, valid even for a singular top matrix. -/
theorem initialForm_det_first_lower_eq_adjugate_trace
    (w : σ → ℤ) (d : ℤ) (b : ι → ι → ℤ)
    (M A B : Matrix ι ι (MvPolynomial σ K))
    (hweights : ∀ π : Equiv.Perm ι, (∑ j : ι, b (π j) j) = d)
    (hM : ∀ i j : ι, IsWeightLE w (b i j) (M i j))
    (hA : ∀ i j : ι, A i j = initialForm w (b i j) (M i j))
    (hB : ∀ i j : ι, B i j = initialForm w (b i j - 1) (M i j)) :
    initialForm w (d - 1) M.det = (A.adjugate * B).trace := by
  rw [initialForm_det_first_lower_eq_updateCols w d b M A B
    hweights hM hA hB]
  exact sum_det_updateCol_eq_adjugate_trace A B

end
end HC4.Polynomial
