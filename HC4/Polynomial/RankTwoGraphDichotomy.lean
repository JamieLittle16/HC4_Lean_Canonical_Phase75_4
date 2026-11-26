import HC4.Polynomial.RankTwoKernelGraph

/-!
# Elementary two-by-two matrix family dichotomy

A family of singular two-by-two matrices with singular pairwise
differences has either a common nonzero right kernel or a common
nonzero left kernel. Factor each member as an outer product;
the determinant of a difference is the negative product of
the two wedges. No algebraic-geometry classification is needed.
-/

namespace HC4.Polynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]

private def graphWedge (u v : Fin 2 → K) : K :=
  u 0 * v 1 - u 1 * v 0

private def graphNormal (u : Fin 2 → K) : Fin 2 → K :=
  ![-u 1, u 0]

private theorem graphNormal_ne_zero (u : Fin 2 → K) (hu : u ≠ 0) :
    graphNormal u ≠ 0 := by
  intro h
  apply hu
  funext i
  have h0 := congrFun h 1
  have h1 := congrFun h 0
  change u 0 = 0 at h0
  change -u 1 = 0 at h1
  fin_cases i
  · exact h0
  · exact neg_eq_zero.mp h1

private theorem graphWedge_swap (u v : Fin 2 → K) :
    graphWedge u v = -graphWedge v u := by
  unfold graphWedge
  ring

private theorem graphWedge_trans_zero (a b c : Fin 2 → K) (ha : a ≠ 0)
    (hab : graphWedge a b = 0) (hac : graphWedge a c = 0) :
    graphWedge b c = 0 := by
  have h (i : Fin 2) : a i * graphWedge b c = 0 := by
    unfold graphWedge at *
    fin_cases i
    · linear_combination b 0 * hac - c 0 * hab
    · linear_combination b 1 * hac - c 1 * hab
  by_contra hn
  apply ha
  funext i
  exact (mul_eq_zero.mp (h i)).resolve_right hn

private def graphOuter (u v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => u i * v j

private theorem graphOuter_det_sub (u v a b : Fin 2 → K) :
    (graphOuter u v - graphOuter a b).det =
      -(graphWedge u a * graphWedge v b) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.sub_apply,graphOuter,graphWedge]
  ring

private theorem graphOuter_factor (A : Matrix (Fin 2) (Fin 2) K)
    (hA : A.det = 0) :
    ∃ u v : Fin 2 → K, A = graphOuter u v ∧ (A = 0 → u = 0 ∧ v = 0) := by
  classical
  by_cases hz : A = 0
  · refine ⟨0,0,?_,fun _ => ⟨rfl,rfl⟩⟩
    rw [hz]
    apply Matrix.ext
    intro i j
    simp [graphOuter]
  have hex : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hz
    apply Matrix.ext
    intro i j
    exact h i j
  obtain ⟨i,j,hij⟩ := hex
  let u : Fin 2 → K := fun a => A a j
  let v : Fin 2 → K := fun b => A i b / A i j
  refine ⟨u,v,?_,fun h => (hz h).elim⟩
  apply Matrix.ext
  intro a b
  change A a b = A a j * (A i b / A i j)
  -- The two-by-two determinant is exactly the needed cross product.
  rw [Matrix.det_fin_two] at hA
  apply mul_right_cancel₀ hij
  calc
    A a b * A i j = A a j * A i b := by
      fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
        first | ring | linear_combination hA | linear_combination -hA
    _ = (A a j * (A i b / A i j)) * A i j := by
      rw [mul_assoc,div_mul_cancel₀ _ hij]

private theorem graphOuter_right_normal (u v c : Fin 2 → K)
    (h : graphWedge c v = 0) :
    graphOuter u v *ᵥ graphNormal c = 0 := by
  funext i
  change (∑ j : Fin 2, graphOuter u v i j * graphNormal c j) = 0
  rw [Fin.sum_univ_two]
  change u i * v 0 * (-c 1) + u i * v 1 * c 0 = 0
  unfold graphWedge at h
  linear_combination u i * h

private theorem graphOuter_left_normal (u v c : Fin 2 → K)
    (h : graphWedge c u = 0) :
    graphNormal c ᵥ* graphOuter u v = 0 := by
  funext j
  change (∑ i : Fin 2, graphNormal c i * graphOuter u v i j) = 0
  rw [Fin.sum_univ_two]
  change (-c 1) * (u 0 * v j) + c 0 * (u 1 * v j) = 0
  unfold graphWedge at h
  linear_combination v j * h

/-- The full singular-difference dichotomy, over any field. -/
theorem rankTwo_singularFamily_commonKernel_or_leftKernel
    {ι : Type*} (B : ι → Matrix (Fin 2) (Fin 2) K)
    (hB : ∀ x, (B x).det = 0)
    (hdiff : ∀ x y, (B x - B y).det = 0) :
    (∃ c : Fin 2 → K, c ≠ 0 ∧ ∀ x, B x *ᵥ c = 0) ∨
      (∃ c : Fin 2 → K, c ≠ 0 ∧ ∀ x, c ᵥ* B x = 0) := by
  classical
  by_cases hzero : ∀ x, B x = 0
  · refine Or.inl ⟨fun _ => 1,?_,?_⟩
    · intro h
      exact one_ne_zero (congrFun h 0)
    · intro x
      rw [hzero x,Matrix.zero_mulVec]
  push_neg at hzero
  obtain ⟨x₀,hx₀⟩ := hzero
  choose u v huv hz using fun x => graphOuter_factor (B x) (hB x)
  have hu₀ : u x₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [huv x₀,h]
    apply Matrix.ext
    intro i j
    simp [graphOuter]
  have hv₀ : v x₀ ≠ 0 := by
    intro h
    apply hx₀
    rw [huv x₀,h]
    apply Matrix.ext
    intro i j
    simp [graphOuter]
  have hp (x y : ι) : graphWedge (u x) (u y) * graphWedge (v x) (v y) = 0 := by
    have h := hdiff x y
    rw [huv x,huv y,graphOuter_det_sub] at h
    exact neg_eq_zero.mp h
  by_cases hall : ∀ x, graphWedge (u x₀) (u x) = 0
  · refine Or.inr ⟨graphNormal (u x₀),graphNormal_ne_zero _ hu₀,?_⟩
    intro x
    rw [huv x]
    exact graphOuter_left_normal _ _ _ (hall x)
  push_neg at hall
  obtain ⟨y,hy⟩ := hall
  have hvy : v y ≠ 0 := by
    intro h
    have hBy : B y = 0 := by
      rw [huv y,h]
      apply Matrix.ext
      intro i j
      simp [graphOuter]
    apply hy
    rw [(hz y hBy).1]
    simp [graphWedge]
  have hxy := (mul_eq_zero.mp (hp x₀ y)).resolve_left hy
  refine Or.inl ⟨graphNormal (v x₀),graphNormal_ne_zero _ hv₀,?_⟩
  intro z
  by_cases hBz : B z = 0
  · rw [hBz,Matrix.zero_mulVec]
  have huz : u z ≠ 0 := by
    intro h
    apply hBz
    rw [huv z,h]
    apply Matrix.ext
    intro i j
    simp [graphOuter]
  have hvz : graphWedge (v x₀) (v z) = 0 := by
    by_contra hn
    have hu0z := (mul_eq_zero.mp (hp x₀ z)).resolve_right hn
    have hvyz : graphWedge (v y) (v z) ≠ 0 := by
      intro h
      apply hn
      apply graphWedge_trans_zero (v y) (v x₀) (v z) hvy _ h
      rw [graphWedge_swap (v y) (v x₀),hxy,neg_zero]
    have huyz := (mul_eq_zero.mp (hp y z)).resolve_right hvyz
    apply hy
    apply graphWedge_trans_zero (u z) (u x₀) (u y) huz
    · rw [graphWedge_swap (u z) (u x₀),hu0z,neg_zero]
    · rw [graphWedge_swap (u z) (u y),huyz,neg_zero]
  rw [huv z]
  exact graphOuter_right_normal _ _ _ hvz

end
end HC4.Polynomial

#print axioms HC4.Polynomial.rankTwo_singularFamily_commonKernel_or_leftKernel
