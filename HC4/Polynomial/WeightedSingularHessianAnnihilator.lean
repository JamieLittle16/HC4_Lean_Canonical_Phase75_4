import HC4.Polynomial.SingularHessianConstantAnnihilator

/-!
# Weight-compatible constant annihilators

For a homogeneous potential, each adjugate entry has its own
row/column weight shift. Consequently an exact weight projection
of a constant annihilator relation is precisely the restriction of
the annihilator to a single equal-weight block.

Combine this with the certified singular-Hessian theorem at any
maximal weighted initial form of positive determinant weight.
The result does not assume a regular transverse block, and the
weight filtration is the actual one on the original source.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [CommRing K]

/-- An adjugate entry is homogeneous at the determinant weight
minus the removed row and column contribution. Use a row update
to retain the existing full determinant API. -/
theorem hessian_adjugate_entry_isWeightedHomogeneous
    (w : σ → ℤ) (m : ℤ) (L : MvPolynomial σ K)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m) (i j : σ) :
    MvPolynomial.IsWeightedHomogeneous w ((hessian L).adjugate i j)
      (((Fintype.card σ : ℤ) - 1) * m - 2 * (∑ k : σ, w k) + w i + w j) := by
  classical
  let A := (hessian L).updateRow j (Pi.single i (1 : MvPolynomial σ K))
  let r : σ → ℤ := fun a => m - w a + if a = j then w i + w j - m else 0
  have hentry (a b : σ) : MvPolynomial.IsWeightedHomogeneous w (A a b)
      (r a - w b) := by
    by_cases ha : a = j
    · subst a
      by_cases hb : b = i
      · subst b
        have he : A j i = 1 := by simp [A, Matrix.updateRow_apply, Pi.single_apply]
        have hr : r j - w i = 0 := by simp [r]; ring
        rw [he, hr]
        exact MvPolynomial.isWeightedHomogeneous_one w
      · have he : A j b = 0 := by simp [A, Matrix.updateRow_apply, Pi.single_apply, hb]
        rw [he]
        exact MvPolynomial.isWeightedHomogeneous_zero w _
    · have he : A a b = hessian L a b := by simp [A, Matrix.updateRow_apply, ha]
      have hr : r a - w b = m - w a - w b := by simp [r, ha]
      rw [he, hr]
      exact hessian_entry_isWeightedHomogeneous hL a b
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
  rw [Matrix.adjugate_apply]
  change MvPolynomial.IsWeightedHomogeneous w A.det _
  apply determinant_isWeightedHomogeneous
  intro π
  have hweights : (∑ b : σ, (r (π b) - w b)) =
      ((Fintype.card σ : ℤ) - 1) * m - 2 * (∑ k : σ, w k) + w i + w j := by
    rw [Finset.sum_sub_distrib, Equiv.sum_comp π r, hsum]
    ring
  rw [← hweights]
  apply MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun b : σ => A (π b) b) (fun b : σ => r (π b) - w b)
  intro b _
  exact hentry (π b) b

/-- The constant adjugate kernel splits along the equal-weight
blocks, without any rank or nonzero cofactor assumption. -/
theorem weighted_adjugate_annihilator_block
    (w : σ → ℤ) (m : ℤ) (L : MvPolynomial σ K)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m)
    (d : σ → K)
    (hd : (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0)
    (s : ℤ) :
    (hessian L).adjugate *ᵥ
      (fun i => MvPolynomial.C (if w i = s then d i else 0)) = 0 := by
  classical
  let A := (hessian L).adjugate
  let B := ((Fintype.card σ : ℤ) - 1) * m - 2 * (∑ k : σ, w k)
  funext i
  have he := congrFun hd i
  change (∑ j : σ, A i j * MvPolynomial.C (d j)) = 0 at he
  have hproj := congrArg (initialForm w (B + w i + s)) he
  rw [map_sum, initialForm_zero] at hproj
  change (∑ j : σ, A i j * MvPolynomial.C (if w j = s then d j else 0)) = 0
  have hterm (j : σ) :
      initialForm w (B + w i + s) (A i j * MvPolynomial.C (d j)) =
        A i j * MvPolynomial.C (if w j = s then d j else 0) := by
    have hh : MvPolynomial.IsWeightedHomogeneous w (A i j) (B + w i + w j) :=
      hessian_adjugate_entry_isWeightedHomogeneous w m L hL i j
    have hh' : MvPolynomial.IsWeightedHomogeneous w
        (A i j * MvPolynomial.C (d j)) (B + w i + w j) := by
      simpa only [add_zero] using hh.mul (MvPolynomial.isWeightedHomogeneous_C w (d j))
    by_cases h : w j = s
    · rw [if_pos h]
      rw [← h]
      exact initialForm_eq_self_of_isWeightedHomogeneous hh'
    · rw [if_neg h, map_zero, mul_zero]
      exact initialForm_eq_zero_of_isWeightedHomogeneous hh' _ (by omega)
  simp only [hterm] at hproj
  exact hproj

namespace RankThreeCubic

variable {F : Type*} [Field F] [CharZero F]

private abbrev I := Unit ⊕ Fin 3
private abbrev S (F : Type*) [Field F] := MvPolynomial I F

/-- Every singular weighted-homogeneous four-variable Hessian
admits a nonzero constant annihilator in one weight block. -/
theorem weightedSingularHessian_exists_block_annihilator
    (w : I → ℤ) (m : ℤ) (L : S F)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m)
    (hdet : (hessian L).det = 0) :
    ∃ (s : ℤ) (d : I → F), d ≠ 0 ∧
      (∀ i, w i ≠ s → d i = 0) ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  obtain ⟨d, hd, ha⟩ := singularHessian_exists_constant_adjugate_annihilator L hdet
  have hex : ∃ i, d i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (funext h)
  obtain ⟨i, hi⟩ := hex
  let b : I → F := fun j => if w j = w i then d j else 0
  refine ⟨w i, b, ?_, ?_, ?_⟩
  · intro h
    apply hi
    have he := congrFun h i
    simpa [b] using he
  · intro j hj
    simp [b, hj]
  · exact weighted_adjugate_annihilator_block w m L hL d ha (w i)

/-- Any actual maximal weighted layer of a constant-Hessian source
at nonzero determinant weight has a weight-compatible annihilator.
Weights need not be the transverse (0,1,1,1) weights. -/
theorem weightedLeading_exists_block_annihilator
    (w : I → ℤ) (m : ℤ) (P : S F)
    (hcap : IsWeightLE w m P)
    (hW : (Fintype.card I : ℤ) * m - 2 * (∑ i : I, w i) ≠ 0)
    {δ : F} (hdet : hessianDeterminant P = MvPolynomial.C δ) :
    let L := initialForm w m P
    ∃ (s : ℤ) (d : I → F), d ≠ 0 ∧
      (∀ i, w i ≠ s → d i = 0) ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  apply weightedSingularHessian_exists_block_annihilator w m _
    (initialForm_isWeightedHomogeneous w m P)
  change hessianDeterminant (initialForm w m P) = 0
  rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m P hcap, hdet]
  exact initialForm_eq_zero_of_isWeightedHomogeneous
    (MvPolynomial.isWeightedHomogeneous_C w δ) _ hW

end RankThreeCubic
end
end HC4.Polynomial

#print axioms HC4.Polynomial.RankThreeCubic.weightedLeading_exists_block_annihilator
