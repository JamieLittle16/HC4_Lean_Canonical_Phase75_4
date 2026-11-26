import HC4.Polynomial.WeightedWallMinorSurvival

/-!
# Highest-weight contraction of a wall annihilator

The exact cofactor component identity is supplemented by its
upper bound. A constant adjugate annihilator of a larger face
then restricts, at its highest occupied old weight, to an
annihilator of the old face. A surviving old cofactor excludes
a unique highest-weight pivot in that direction.

The statements concern actual polynomial faces and do not
assume a wall-crossing or descent algorithm terminates.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {σ ι K : Type*} [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  [CommRing K]

private theorem wall_weightLE_sum {α : Type*}
    (w : σ → ℤ) (m : ℤ) (s : Finset α)
    (f : α → MvPolynomial σ K)
    (h : ∀ i ∈ s, IsWeightLE w m (f i)) :
    IsWeightLE w m (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (by simp)).add (ih (fun i hi => h i (by simp [hi])))

/-- The determinant respects additive row and column weight bounds. -/
theorem wall_det_isWeightLE
    (w : σ → ℤ) (r c : ι → ℤ)
    (A : Matrix ι ι (MvPolynomial σ K))
    (h : ∀ i j, IsWeightLE w (r i + c j) (A i j)) :
    IsWeightLE w ((∑ i : ι, r i) + ∑ j : ι, c j) A.det := by
  classical
  rw [Matrix.det_apply']
  apply wall_weightLE_sum
  intro π _
  have hp := isWeightLE_prod Finset.univ w
    (fun j : ι => r (π j) + c j) (fun j => A (π j) j)
    (fun j _ => h (π j) j)
  rw [Finset.sum_add_distrib, Equiv.sum_comp π r] at hp
  let a : K := ↑↑(Equiv.Perm.sign π)
  change IsWeightLE w ((∑ i : ι, r i) + ∑ j : ι, c j)
    (MvPolynomial.C a * ∏ j : ι, A (π j) j)
  simpa only [zero_add] using
    (isWeightLE_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_C w a)).mul hp

variable [Fintype σ]

/-- Each adjugate entry of a bounded source has the cofactor weight
as an upper bound, including in the presence of lower layers. -/
theorem wall_hessian_adjugate_isWeightLE
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P) (i j : σ) :
    IsWeightLE w (((Fintype.card σ : ℤ) - 1) * m -
      2 * (∑ k : σ, w k) + w i + w j) ((hessian P).adjugate i j) := by
  classical
  let A := (hessian P).updateRow j (Pi.single i (1 : MvPolynomial σ K))
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
  rw [Matrix.adjugate_apply]
  change IsWeightLE w _ A.det
  rw [← hw]
  apply wall_det_isWeightLE w r (fun b : σ => -w b)
  intro a b
  by_cases ha : a = j
  · subst a
    by_cases hb : b = i
    · subst b
      have he : A j i = 1 := by simp [A, Matrix.updateRow_apply]
      have hr : r j + -w i = 0 := by simp [r]
      rw [he, hr]
      exact isWeightLE_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_one K w)
    · have he : A j b = 0 := by simp [A, Matrix.updateRow_apply, hb]
      rw [he]
      exact isWeightLE_zero w _
  · have he : A a b = hessian P a b := by simp [A, Matrix.updateRow_apply, ha]
    rw [he, show r a + -w b = m - w a - w b by simp [r, ha, sub_eq_add_neg]]
    exact hcap.hessian_entry a b

/-- The highest occupied old-weight block of a constant annihilator
of the enlarged face is a constant annihilator of the old face. -/
theorem wall_adjugate_annihilator_topBlock
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P) (d : σ → K) (s : ℤ)
    (hmax : ∀ j, d j ≠ 0 → w j ≤ s)
    (hd : (hessian P).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0) :
    (hessian (initialForm w m P)).adjugate *ᵥ
      (fun i => MvPolynomial.C (if w i = s then d i else 0)) = 0 := by
  classical
  let B := ((Fintype.card σ : ℤ) - 1) * m - 2 * (∑ k : σ, w k)
  funext i
  have he := congrFun hd i
  change (∑ j : σ, (hessian P).adjugate i j * MvPolynomial.C (d j)) = 0 at he
  have hp := congrArg (initialForm w (B + w i + s)) he
  rw [map_sum, initialForm_zero] at hp
  have hterm (j : σ) :
      initialForm w (B + w i + s) ((hessian P).adjugate i j * MvPolynomial.C (d j)) =
        (hessian (initialForm w m P)).adjugate i j *
          MvPolynomial.C (if w j = s then d j else 0) := by
    by_cases hz : d j = 0
    · simp [hz]
    by_cases hj : w j = s
    · rw [if_pos hj, ← hj]
      rw [mul_comm ((hessian P).adjugate i j), MvPolynomial.C_mul', initialForm_smul]
      have h := initialForm_hessian_adjugate_entry w m P hcap i j
      change initialForm w (B + w i + w j) ((hessian P).adjugate i j) =
        (hessian (initialForm w m P)).adjugate i j at h
      rw [h, ← MvPolynomial.C_mul', mul_comm]
    · rw [if_neg hj, map_zero, mul_zero]
      have hb : IsWeightLE w (B + w i + w j) ((hessian P).adjugate i j) :=
        wall_hessian_adjugate_isWeightLE w m P hcap i j
      have hb' : IsWeightLE w (B + w i + w j)
          ((hessian P).adjugate i j * MvPolynomial.C (d j)) := by
        simpa only [add_zero] using
          hb.mul (isWeightLE_of_isWeightedHomogeneous (MvPolynomial.isWeightedHomogeneous_C w (d j)))
      have hle := hmax j hz
      exact initialForm_eq_zero_of_isWeightLE hb' (by omega)
  simp only [hterm] at hp
  exact hp

variable [IsDomain K]

/-- If a coordinate is the unique highest-weight occupied direction
of a wall annihilator, its entire old cofactor column must vanish. -/
theorem wall_unique_top_annihilator_forces_zero_column
    (w : σ → ℤ) (m : ℤ) (P : MvPolynomial σ K)
    (hcap : IsWeightLE w m P) (d : σ → K) (k : σ)
    (hk : d k ≠ 0)
    (htop : ∀ j, j ≠ k → d j ≠ 0 → w j < w k)
    (hd : (hessian P).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0) :
    ∀ i, (hessian (initialForm w m P)).adjugate i k = 0 := by
  classical
  have hmax (j : σ) (hj : d j ≠ 0) : w j ≤ w k := by
    by_cases h : j = k
    · rw [h]
    · exact le_of_lt (htop j h hj)
  have h := wall_adjugate_annihilator_topBlock w m P hcap d (w k) hmax hd
  intro i
  have hi := congrFun h i
  change (∑ j : σ, (hessian (initialForm w m P)).adjugate i j *
    MvPolynomial.C (if w j = w k then d j else 0)) = 0 at hi
  rw [Finset.sum_eq_single k] at hi
  · simp only [if_pos rfl] at hi
    exact (mul_eq_zero.mp hi).resolve_right (MvPolynomial.C_ne_zero.mpr hk)
  · intro j _ hj
    by_cases hz : d j = 0
    · simp [hz]
    · have hn : w j ≠ w k := ne_of_lt (htop j hj hz)
      simp [hn]
  · simp

end
end HC4.Polynomial

#print axioms HC4.Polynomial.wall_adjugate_annihilator_topBlock
#print axioms HC4.Polynomial.wall_unique_top_annihilator_forces_zero_column
