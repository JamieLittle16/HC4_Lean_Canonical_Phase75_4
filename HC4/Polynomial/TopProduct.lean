import HC4.Polynomial.DerivativeBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Top weighted component of finite products

If each factor has a prescribed weak upper weight and a chosen homogeneous
top part, and the difference is strictly lower, then the product has the
product of the top parts as its exact component at the sum of the bounds.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ K ι : Type*} [CommRing K] [DecidableEq σ]

/-- A finite product of weakly bounded factors is weakly bounded by the sum. -/
theorem isWeightLE_prod
    (s : Finset ι) (w : σ → ℤ) (b : ι → ℤ)
    (f : ι → MvPolynomial σ K)
    (hf : ∀ i ∈ s, IsWeightLE w (b i) (f i)) :
    IsWeightLE w (∑ i ∈ s, b i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (isWeightLE_of_isWeightedHomogeneous
          (MvPolynomial.isWeightedHomogeneous_C w (1 : K)))
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))

/-- If one distinguished factor is strictly lower and all others are weakly bounded,
then the whole finite product is strictly lower than the sum bound. -/
theorem isWeightLT_prod_of_exists
    (s : Finset ι) (w : σ → ℤ) (b : ι → ℤ)
    (f : ι → MvPolynomial σ K)
    (hfLE : ∀ i ∈ s, IsWeightLE w (b i) (f i))
    (i0 : ι) (hi0 : i0 ∈ s)
    (hi0LT : IsWeightLT w (b i0) (f i0)) :
    IsWeightLT w (∑ i ∈ s, b i) (∏ i ∈ s, f i) := by
  classical
  have hsplit : s = insert i0 (s.erase i0) := by
    exact (Finset.insert_erase hi0).symm
  rw [hsplit, Finset.prod_insert (Finset.notMem_erase i0 s), Finset.sum_insert (Finset.notMem_erase i0 s)]
  apply hi0LT.mul_le
  apply isWeightLE_prod
  intro i hi
  exact hfLE i (Finset.mem_of_mem_erase hi)

/-- A telescoping product identity: if every factor differs from its chosen top part
by a strict lower-weight term, then the product difference is strictly lower. -/
theorem prod_sub_prod_isWeightLT
    (s : Finset ι) (w : σ → ℤ) (b : ι → ℤ)
    (f g : ι → MvPolynomial σ K)
    (hf : ∀ i ∈ s, IsWeightLE w (b i) (f i))
    (hg : ∀ i ∈ s, IsWeightLE w (b i) (g i))
    (hdiff : ∀ i ∈ s, IsWeightLT w (b i) (f i - g i)) :
    IsWeightLT w (∑ i ∈ s, b i)
      ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hfa := hf a (by simp)
      have hga := hg a (by simp)
      have hda := hdiff a (by simp)
      have hfrest : IsWeightLE w (∑ i ∈ s, b i) (∏ i ∈ s, f i) := by
        apply isWeightLE_prod
        intro i hi
        exact hf i (by simp [hi])
      have hgrest : IsWeightLE w (∑ i ∈ s, b i) (∏ i ∈ s, g i) := by
        apply isWeightLE_prod
        intro i hi
        exact hg i (by simp [hi])
      have hirest : IsWeightLT w (∑ i ∈ s, b i)
          ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) := by
        exact ih
          (fun i hi => hf i (by simp [hi]))
          (fun i hi => hg i (by simp [hi]))
          (fun i hi => hdiff i (by simp [hi]))
      have h1 : IsWeightLT w (b a + ∑ i ∈ s, b i)
          ((f a - g a) * (∏ i ∈ s, f i)) := hda.mul_le hfrest
      have h2 : IsWeightLT w (b a + ∑ i ∈ s, b i)
          (g a * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i))) := hga.mul_lt hirest
      have hsum := h1.add h2
      convert hsum using 1 <;> ring

/-- Exact top component of a finite product. -/
theorem initialForm_prod_eq_prod
    (s : Finset ι) (w : σ → ℤ) (b : ι → ℤ)
    (f g : ι → MvPolynomial σ K)
    (hgHom : ∀ i ∈ s, MvPolynomial.IsWeightedHomogeneous w (g i) (b i))
    (hdiff : ∀ i ∈ s, IsWeightLT w (b i) (f i - g i)) :
    initialForm w (∑ i ∈ s, b i) (∏ i ∈ s, f i) = ∏ i ∈ s, g i := by
  classical
  have hgLE : ∀ i ∈ s, IsWeightLE w (b i) (g i) :=
    fun i hi => isWeightLE_of_isWeightedHomogeneous (hgHom i hi)
  have hfLE : ∀ i ∈ s, IsWeightLE w (b i) (f i) := by
    intro i hi
    have hsum : f i = (f i - g i) + g i := by ring
    rw [hsum]
    exact (hdiff i hi).isWeightLE.add (hgLE i hi)
  have hprodDiff := prod_sub_prod_isWeightLT s w b f g hfLE hgLE hdiff
  have hzero := initialForm_eq_zero_of_isWeightLT hprodDiff (le_refl _)
  have hgProdHom : MvPolynomial.IsWeightedHomogeneous w (∏ i ∈ s, g i)
      (∑ i ∈ s, b i) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod s g b
    exact hgHom
  have htop := initialForm_eq_self_of_isWeightedHomogeneous hgProdHom
  have hdecomp : (∏ i ∈ s, f i) =
      ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) + (∏ i ∈ s, g i) := by ring
  rw [hdecomp, initialForm_add, hzero, htop, zero_add]

end

end HC4.Polynomial
