import HC4.Polynomial.WeightedComplementaryKernel

/-!
# Exact minor survival at a weighted wall

All minors of a Hessian have an exact top component obtained from
the genuine maximal layer, with the row and column weights subtracted.
The adjugate version follows by replacing one row by a coordinate row.

Consequently the highest old-weight part of any constant adjugate
annihilator of a wall form annihilates the old leading adjugate.
In particular a unique highest-weight nonzero coordinate cannot
have a surviving principal cofactor in the old layer.

This is a source-level wall constraint, not a termination theorem.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {σ ι K : Type*} [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  [CommRing K]

/-- Exact determinant extraction with additive row and column
weight bounds. No invertibility hypotheses. -/
theorem initialForm_det_of_rowColumn_weights
    (w : σ → ℤ) (r c : ι → ℤ)
    (A B : Matrix ι ι (MvPolynomial σ K))
    (hhom : ∀ i j, MvPolynomial.IsWeightedHomogeneous w (B i j) (r i + c j))
    (hdiff : ∀ i j, IsWeightLT w (r i + c j) (A i j - B i j)) :
    initialForm w ((∑ i : ι, r i) + ∑ j : ι, c j) A.det = B.det := by
  classical
  rw [Matrix.det_apply', Matrix.det_apply', map_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hweights : (∑ j : ι, (r (π j) + c j)) =
      (∑ i : ι, r i) + ∑ j : ι, c j := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp π r]
  have hp :
      initialForm w ((∑ i : ι, r i) + ∑ j : ι, c j)
        (∏ j : ι, A (π j) j) = ∏ j : ι, B (π j) j := by
    rw [← hweights]
    exact initialForm_prod_eq_prod Finset.univ w
      (fun j : ι => r (π j) + c j)
      (fun j => A (π j) j) (fun j => B (π j) j)
      (fun j _ => hhom (π j) j) (fun j _ => hdiff (π j) j)
  let a : K := ↑↑(Equiv.Perm.sign π)
  change initialForm w ((∑ i : ι, r i) + ∑ j : ι, c j)
      (MvPolynomial.C a * ∏ j : ι, A (π j) j) =
    MvPolynomial.C a * ∏ j : ι, B (π j) j
  simp only [MvPolynomial.C_mul', initialForm_smul, hp]

/-- All coordinate minors, including nonprincipal minors, survive
as exact components at their appropriate old weight. -/
theorem initialForm_hessian_minor
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P) (u v : ι → σ) :
    initialForm w ((Fintype.card ι : ℤ) * m -
        (∑ i : ι, w (u i)) - ∑ j : ι, w (v j))
      ((hessian P).submatrix u v).det =
      ((hessian (initialForm w m P)).submatrix u v).det := by
  classical
  have hweights : (∑ i : ι, (m - w (u i))) + (∑ j : ι, -w (v j)) =
      (Fintype.card ι : ℤ) * m - (∑ i : ι, w (u i)) - ∑ j : ι, w (v j) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [← hweights]
  apply initialForm_det_of_rowColumn_weights w
    (fun i : ι => m - w (u i)) (fun j : ι => -w (v j))
  · intro i j
    change MvPolynomial.IsWeightedHomogeneous w
      (hessian (initialForm w m P) (u i) (v j)) (m - w (u i) + -w (v j))
    rw [← sub_eq_add_neg]
    exact hessian_entry_isWeightedHomogeneous
      (initialForm_isWeightedHomogeneous w m P) (u i) (v j)
  · intro i j
    change IsWeightLT w (m - w (u i) + -w (v j))
      (hessian P (u i) (v j) - hessian (initialForm w m P) (u i) (v j))
    rw [← sub_eq_add_neg, hessian_initialForm_entry]
    exact sub_initialForm_isWeightLT (hcap.hessian_entry (u i) (v j))

variable [Fintype σ]

/-- Adjugate entries have the old leading cofactor as their exact
component, even when that cofactor vanishes. -/
theorem initialForm_hessian_adjugate_entry
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P) (i j : σ) :
    initialForm w (((Fintype.card σ : ℤ) - 1) * m -
      2 * (∑ k : σ, w k) + w i + w j) ((hessian P).adjugate i j) =
      (hessian (initialForm w m P)).adjugate i j := by
  classical
  let L := initialForm w m P
  let A := (hessian P).updateRow j (Pi.single i (1 : MvPolynomial σ K))
  let B := (hessian L).updateRow j (Pi.single i (1 : MvPolynomial σ K))
  let r : σ → ℤ := fun a => m - w a + if a = j then w i + w j - m else 0
  have hsum : (∑ a : σ, r a) =
      (Fintype.card σ : ℤ) * m - (∑ a : σ, w a) + (w i + w j - m) := by
    simp only [r, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  have hw : (∑ a : σ, r a) + (∑ b : σ, -w b) =
      ((Fintype.card σ : ℤ) - 1) * m - 2 * (∑ k : σ, w k) + w i + w j := by
    rw [hsum, Finset.sum_neg_distrib]
    ring
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  change initialForm w _ A.det = B.det
  rw [← hw]
  apply initialForm_det_of_rowColumn_weights w r (fun b : σ => -w b)
  · intro a b
    by_cases ha : a = j
    · subst a
      by_cases hb : b = i
      · subst b
        have he : B j i = 1 := by simp [B, Matrix.updateRow_apply]
        have hr : r j + -w i = 0 := by simp [r]
        rw [he, hr]
        exact MvPolynomial.isWeightedHomogeneous_one K w
      · have he : B j b = 0 := by simp [B, Matrix.updateRow_apply, hb]
        rw [he]
        exact MvPolynomial.isWeightedHomogeneous_zero K w _
    · have he : B a b = hessian L a b := by simp [B, Matrix.updateRow_apply, ha]
      rw [he, show r a + -w b = m - w a - w b by simp [r, ha, sub_eq_add_neg]]
      exact hessian_entry_isWeightedHomogeneous
        (initialForm_isWeightedHomogeneous w m P) a b
  · intro a b
    by_cases ha : a = j
    · subst a
      have he : A j b = B j b := by simp [A, B, Matrix.updateRow_apply]
      rw [he, sub_self]
      exact isWeightLT_zero w _
    · have he : A a b = hessian P a b := by simp [A, Matrix.updateRow_apply, ha]
      have he' : B a b = hessian L a b := by simp [B, Matrix.updateRow_apply, ha]
      rw [he, he', show r a + -w b = m - w a - w b by simp [r, ha, sub_eq_add_neg]]
      change IsWeightLT w (m - w a - w b)
        (hessian P a b - hessian (initialForm w m P) a b)
      rw [hessian_initialForm_entry]
      exact sub_initialForm_isWeightLT (hcap.hessian_entry a b)

/-- A surviving minor cannot disappear on adjoining terms strictly
below the old maximal weight. -/
theorem hessian_minor_ne_zero_of_initialForm
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P) (u v : ι → σ)
    (h : ((hessian (initialForm w m P)).submatrix u v).det ≠ 0) :
    ((hessian P).submatrix u v).det ≠ 0 := by
  intro hz
  apply h
  rw [← initialForm_hessian_minor w m P hcap u v, hz, initialForm_zero]

end
end HC4.Polynomial

#print axioms HC4.Polynomial.initialForm_hessian_minor
#print axioms HC4.Polynomial.initialForm_hessian_adjugate_entry
