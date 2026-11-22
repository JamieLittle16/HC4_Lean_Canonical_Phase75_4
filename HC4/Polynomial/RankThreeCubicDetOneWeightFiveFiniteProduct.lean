import HC4.Polynomial.RankThreeCubicDetOneWeightFiveBoundedProduct
import HC4.Polynomial.TopProduct
import Mathlib.Tactic

/-!
# First lower component of an arbitrary finite weighted product

If f_i has upper weight b_i, the weight (sum b_i)-1 component
of the product of all f_i is the sum over i of the exact
(b_i-1) component at i multiplied by the top components of
all other factors.

The proof inducts using the arbitrary bounded two-factor formula,
and includes the empty-product case (its weight -1 part vanishes).
This result is intended for the four-factor Leibniz determinant terms.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {σ K ι : Type*} [CommRing K] [DecidableEq σ] [DecidableEq ι]

theorem initialForm_prod_first_lower
    (s : Finset ι) (w : σ → ℤ) (b : ι → ℤ)
    (f : ι → MvPolynomial σ K)
    (hf : ∀ i ∈ s, IsWeightLE w (b i) (f i)) :
    initialForm w ((∑ i ∈ s, b i) - 1) (∏ i ∈ s, f i) =
      ∑ i ∈ s, initialForm w (b i - 1) (f i) *
        ∏ j ∈ s.erase i, initialForm w (b j) (f j) := by
  classical
  let g : ι → MvPolynomial σ K :=
    fun i => initialForm w (b i) (f i)
  let h : ι → MvPolynomial σ K :=
    fun i => initialForm w (b i - 1) (f i)
  change initialForm w ((∑ i ∈ s, b i) - 1) (∏ i ∈ s, f i) =
      ∑ i ∈ s, h i * ∏ j ∈ s.erase i, g j
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Finset.prod_empty, zero_sub]
      exact initialForm_eq_zero_of_isWeightedHomogeneous
        (MvPolynomial.isWeightedHomogeneous_C w (1 : K))
        (-1) (by norm_num)
  | @insert a s ha ih =>
      have hfa : IsWeightLE w (b a) (f a) :=
        hf a (Finset.mem_insert_self a s)
      have hfr : ∀ i ∈ s, IsWeightLE w (b i) (f i) := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hrest : IsWeightLE w (∑ i ∈ s, b i)
          (∏ i ∈ s, f i) := isWeightLE_prod s w b f hfr
      have htop :
          initialForm w (∑ i ∈ s, b i) (∏ i ∈ s, f i) =
            ∏ i ∈ s, g i := by
        exact initialForm_prod_eq_prod s w b f g
          (fun i _ => initialForm_isWeightedHomogeneous w (b i) (f i))
          (fun i hi => sub_initialForm_isWeightLT (hfr i hi))
      have ih' :
          initialForm w ((∑ i ∈ s, b i) - 1)
              (∏ i ∈ s, f i) =
            ∑ i ∈ s, h i * ∏ j ∈ s.erase i, g j :=
        ih hfr
      have hother (i : ι) (hi : i ∈ s) :
          (∏ j ∈ (insert a s).erase i, g j) =
            g a * ∏ j ∈ s.erase i, g j := by
        have hai : a ≠ i := by
          intro heq
          apply ha
          exact heq ▸ hi
        rw [Finset.erase_insert_of_ne hai,
          Finset.prod_insert (by
            intro hm
            exact ha (Finset.mem_of_mem_erase hm))]
      have hsum :
          (∑ i ∈ s, h i * ∏ j ∈ (insert a s).erase i, g j) =
            g a * (∑ i ∈ s, h i * ∏ j ∈ s.erase i, g j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hother i hi]
        ring
      calc
        initialForm w ((∑ i ∈ insert a s, b i) - 1)
            (∏ i ∈ insert a s, f i) =
          initialForm w (b a + (∑ i ∈ s, b i) - 1)
            (f a * ∏ i ∈ s, f i) := by
            rw [Finset.sum_insert ha, Finset.prod_insert ha]
        _ = g a * (∑ i ∈ s, h i * ∏ j ∈ s.erase i, g j) +
            h a * ∏ i ∈ s, g i := by
            rw [initialForm_mul_first_lower
              w (b a) (∑ i ∈ s, b i) (f a)
                (∏ i ∈ s, f i) hfa hrest]
            change g a * initialForm w ((∑ i ∈ s, b i) - 1)
                (∏ i ∈ s, f i) +
              h a * initialForm w (∑ i ∈ s, b i)
                (∏ i ∈ s, f i) = _
            rw [ih', htop]
        _ = ∑ i ∈ insert a s, h i *
            ∏ j ∈ (insert a s).erase i, g j := by
            rw [Finset.sum_insert ha, Finset.erase_insert ha, hsum]
            ring

end
end HC4.Polynomial
