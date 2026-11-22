import HC4.Polynomial.RankThreeCubicDetOneFirstCorrectionBlocks
import HC4.Polynomial.TopProduct
import Mathlib.Tactic

/-!
# A one-extra-weight determinant-product gap

The leading 4x4 cubic Hessian determinant has transverse weight 6.
The desired first lower coefficient lives at weight 5. A factor
coming from the source remainder of weight below 2 has a Hessian
entry at least two weights below the corresponding cubic entry;
thus any product with such a factor has weight strictly below 5.

This module first proves the FINITE PRODUCT gap lemma uniformly,
without expanding any 4x4 determinant. The product lemma is a
reusable algebraic ingredient for excluding the low remainder
from the weight-five coefficient in a subsequent theorem.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {σ K ι : Type*} [CommRing K] [DecidableEq σ]

/-- If the difference between matching factors has one *extra*
degree of strictness, then the difference between the products
also has one extra degree of strictness. In an integer-weighted
ring, a difference strictly below `b_i-1` is at least two degrees
below the nominal top bound `b_i`. -/
theorem prod_sub_prod_isWeightLT_gapOne
    (s : Finset ι) (w : σ → ℤ) (b : ι → ℤ)
    (f g : ι → MvPolynomial σ K)
    (hf : ∀ i ∈ s, IsWeightLE w (b i) (f i))
    (hg : ∀ i ∈ s, IsWeightLE w (b i) (g i))
    (hdiff : ∀ i ∈ s, IsWeightLT w (b i - 1) (f i - g i)) :
    IsWeightLT w ((∑ i ∈ s, b i) - 1)
      ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      have hfa := hf a (by simp)
      have hga := hg a (by simp)
      have hda := hdiff a (by simp)
      have hfr : IsWeightLE w (∑ i ∈ s, b i)
          (∏ i ∈ s, f i) :=
        isWeightLE_prod s w b f (fun i hi => hf i (by simp [hi]))
      have hgr : IsWeightLE w (∑ i ∈ s, b i)
          (∏ i ∈ s, g i) :=
        isWeightLE_prod s w b g (fun i hi => hg i (by simp [hi]))
      have hidr : IsWeightLT w ((∑ i ∈ s, b i) - 1)
          ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) :=
        ih (fun i hi => hf i (by simp [hi]))
          (fun i hi => hg i (by simp [hi]))
          (fun i hi => hdiff i (by simp [hi]))
      have h1 : IsWeightLT w
          ((b a - 1) + ∑ i ∈ s, b i)
          ((f a - g a) * ∏ i ∈ s, f i) :=
        hda.mul_le hfr
      have h2 : IsWeightLT w
          (b a + ((∑ i ∈ s, b i) - 1))
          (g a * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i))) :=
        hga.mul_lt hidr
      have hsum := h1.add (by
        convert h2 using 1 <;> ring)
      convert hsum using 1 <;> ring

end
end HC4.Polynomial
