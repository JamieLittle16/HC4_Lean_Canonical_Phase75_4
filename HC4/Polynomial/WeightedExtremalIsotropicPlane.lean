module

public import HC4.Polynomial.RankOneHessianClosure

/-!
# Arbitrary constant affine-plane exclusion at the global optimum

A two-dimensional constant totally isotropic subspace of the leading
Hessian need not initially be compatible with the weights. Take the
highest occupied weight block of each of two vectors, after eliminating
one pivot from the second. The lowest weight in their Hessian contraction
isolates exactly the pair of highest blocks.

These blocks are independent, and two weight-compatible determinant-one
column shears align them simultaneously. The verified coordinate-plane
obstruction then excludes the original subspace.

This does not assert that every variable-kernel Hessian has such a plane.
-/

@[expose] public section

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
abbrev WeightedExtremalIsotropicPlane.S (K : Type*) [Field K] := MvPolynomial (Fin 4) K

open WeightedExtremalIsotropicPlane (S)

/-- The polynomial contraction of the Hessian with two constant vectors. -/
def extremalHessianPair (L : S K) (d e : Fin 4 → K) : S K :=
  ∑ i : Fin 4, ∑ j : Fin 4, MvPolynomial.C (d i) * hessian L i j * MvPolynomial.C (e j)

def extremalWeightBlock (w : Fin 4 → ℤ) (s : ℤ) (d : Fin 4 → K) : Fin 4 → K :=
  fun i => if w i = s then d i else 0

/-- The top occupied blocks of both vectors isolate the lowest weight
component of the Hessian contraction. -/
theorem extremalHessianPair_topBlocks
    (L : S K) (w : Fin 4 → ℤ) (m s t : ℤ)
    (hL : MvPolynomial.IsWeightedHomogeneous w L m) (d e : Fin 4 → K)
    (hd : ∀ i, d i ≠ 0 → w i ≤ s) (he : ∀ j, e j ≠ 0 → w j ≤ t) :
    extremalHessianPair L (extremalWeightBlock w s d) (extremalWeightBlock w t e) =
      initialForm w (m-s-t) (extremalHessianPair L d e) := by
  classical
  unfold extremalHessianPair
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hh : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (d i) * hessian L i j * MvPolynomial.C (e j)) (m-w i-w j) := by
    simpa only [zero_add, add_zero] using
      ((MvPolynomial.isWeightedHomogeneous_C w (d i)).mul
        (hessian_entry_isWeightedHomogeneous hL i j)).mul
        (MvPolynomial.isWeightedHomogeneous_C w (e j))
  by_cases hdi : d i = 0
  · simp [extremalWeightBlock, hdi]
  by_cases hej : e j = 0
  · simp [extremalWeightBlock, hej]
  have hwi := hd i hdi
  have hwj := he j hej
  by_cases hi : w i = s
  · by_cases hj : w j = t
    · simp only [extremalWeightBlock, hi, hj, if_true]
      have hh' : MvPolynomial.IsWeightedHomogeneous w
          (MvPolynomial.C (d i) * hessian L i j * MvPolynomial.C (e j)) (m-s-t) := by
        rw [← hi, ← hj]
        exact hh
      exact (initialForm_eq_self_of_isWeightedHomogeneous hh').symm
    · simp only [extremalWeightBlock, if_pos hi, if_neg hj, map_zero, mul_zero]
      have hne : m-s-t ≠ m-w i-w j := by omega
      exact (initialForm_eq_zero_of_isWeightedHomogeneous hh (m-s-t) hne).symm
  · simp only [extremalWeightBlock, if_neg hi, map_zero, zero_mul]
    have hne : m-s-t ≠ m-w i-w j := by omega
    exact (initialForm_eq_zero_of_isWeightedHomogeneous hh (m-s-t) hne).symm

/-- Scalar normalization does not affect vanishing of the contraction. -/
theorem extremalHessianPair_scale
    (L : S K) (d e : Fin 4 → K) (a b : K) :
    extremalHessianPair L (fun i => a*d i) (fun i => b*e i) =
      MvPolynomial.C a * extremalHessianPair L d e * MvPolynomial.C b := by
  classical
  unfold extremalHessianPair
  simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every nonzero vector has a maximal occupied weight. -/
theorem extremal_exists_topWeight_pivot
    (w : Fin 4 → ℤ) (d : Fin 4 → K) (hd : d ≠ 0) :
    ∃ k : Fin 4, d k ≠ 0 ∧ ∀ i, d i ≠ 0 → w i ≤ w k := by
  classical
  have hne : (Finset.univ.filter (fun i : Fin 4 => d i ≠ 0)).Nonempty := by
    have hex : ∃ i, d i ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hd (funext hn)
    obtain ⟨i,hi⟩ := hex
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image _ w hne
  exact ⟨k,(Finset.mem_filter.mp hk).2,
    fun i hi => hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)⟩

/-- Away from its selected column the kernel shear is the identity. -/
theorem extremalKernelShear_other_column
    (d : Fin 4 → K) (k i j : Fin 4) (hj : j ≠ k) :
    extremalKernelShear d k i j = (1 : Matrix (Fin 4) (Fin 4) K) i j := by
  classical
  simp [extremalKernelShear, annihilatorShear, Matrix.updateRow_apply,
    hj, Matrix.one_apply, eq_comm]

/-- A vector with zero pivot entry is fixed by the column shear. -/
theorem extremalKernelShear_mulVec_of_zero
    (d e : Fin 4 → K) (k : Fin 4) (he : e k = 0) :
    extremalKernelShear d k *ᵥ e = e := by
  classical
  have h : extremalKernelShear d k *ᵥ e = (1 : Matrix (Fin 4) (Fin 4) K) *ᵥ e := by
    funext i
    change (∑ j : Fin 4, extremalKernelShear d k i j * e j) =
      ∑ j : Fin 4, (1 : Matrix (Fin 4) (Fin 4) K) i j * e j
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = k
    · subst j
      rw [he, mul_zero, mul_zero]
    · rw [extremalKernelShear_other_column d k i j hj]
  rw [h, Matrix.one_mulVec]

/-- Two normalized block directions, with the first pivot eliminated
from the second, extend to a determinant-one weight-compatible chart. -/
theorem extremal_align_two_blocks
    (w : Fin 4 → ℤ) (d e : Fin 4 → K) (k l : Fin 4) (hkl : k ≠ l)
    (hdk : d k = 1) (hel : e l = 1) (hek : e k = 0)
    (hd : ∀ i, w i ≠ w k → d i = 0)
    (he : ∀ i, w i ≠ w l → e i = 0) :
    ∃ N : Matrix (Fin 4) (Fin 4) K, N.det = 1 ∧
      (∀ i j, w i ≠ w j → N i j = 0) ∧
      (∀ i, N i k = d i) ∧ (∀ i, N i l = e i) := by
  classical
  let A := extremalKernelShear d k
  let B := extremalKernelShear e l
  have hA : ∀ i j, w i ≠ w j → A i j = 0 :=
    extremalKernelShear_respects_weight w d k hd
  have hB : ∀ i j, w i ≠ w j → B i j = 0 :=
    extremalKernelShear_respects_weight w e l he
  have hAk (i : Fin 4) : A i k = d i := by
    change extremalKernelShear d k i k = d i
    rw [extremalKernelShear_column d k (by rw [hdk]; exact one_ne_zero), hdk, div_one]
  have hBl (i : Fin 4) : B i l = e i := by
    change extremalKernelShear e l i l = e i
    rw [extremalKernelShear_column e l (by rw [hel]; exact one_ne_zero), hel, div_one]
  refine ⟨A*B, by rw [Matrix.det_mul]; simp [A,B,extremalKernelShear_det], ?_, ?_, ?_⟩
  · intro i j hij
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hia : w i = w a
    · have haj : w a ≠ w j := by intro h; exact hij (hia.trans h)
      rw [hB a j haj, mul_zero]
    · rw [hA i a hia, zero_mul]
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · have hb : B k k = 1 := by
        change extremalKernelShear e l k k = 1
        rw [extremalKernelShear_other_column e l k k hkl, Matrix.one_apply_eq]
      rw [hb, mul_one, hAk]
    · intro j _ hj
      have hb : B j k = 0 := by
        change extremalKernelShear e l j k = 0
        rw [extremalKernelShear_other_column e l j k hkl]
        simp [Matrix.one_apply, hj]
      rw [hb, mul_zero]
    · simp
  · intro i
    rw [Matrix.mul_apply]
    simp only [hBl]
    exact congrFun (extremalKernelShear_mulVec_of_zero d e k hek) i

/-- Hessian covariance expressed directly as a contraction with the
two constant columns of the source chart. -/
theorem extremalHessianPair_chart_entry
    (L : S K) (N : Matrix (Fin 4) (Fin 4) K) (k l : Fin 4) :
    hessian (weightedLinearSubstitution N L) k l =
      weightedLinearSubstitution N (extremalHessianPair L (fun i => N i k) (fun i => N i l)) := by
  classical
  let f := weightedLinearSubstitution N
  let C : K →+* S K := MvPolynomial.C
  have hC (a : K) : f (C a) = C a := f.commutes a
  rw [weightedLinearSubstitution_hessian]
  change (∑ j : Fin 4, (∑ i : Fin 4, C (N i k) * f (hessian L i j)) * C (N j l)) =
    f (extremalHessianPair L (fun i => N i k) (fun i => N i l))
  calc
    _ = ∑ j : Fin 4, ∑ i : Fin 4, C (N i k) * f (hessian L i j) * C (N j l) := by
      simp only [Finset.sum_mul]
    _ = ∑ i : Fin 4, ∑ j : Fin 4, C (N i k) * f (hessian L i j) * C (N j l) :=
      Finset.sum_comm
    _ = f (extremalHessianPair L (fun i => N i k) (fun i => N i l)) := by
      change _ = f (∑ i : Fin 4, ∑ j : Fin 4, C (N i k) * hessian L i j * C (N j l))
      simp only [map_sum, map_mul, hC]

set_option maxHeartbeats 4000000 in
/-- No constant two-plane on which the leading Hessian form vanishes
identically can exist at a positive-clock global optimum. The plane is
not assumed to be weight graded. -/
theorem globalWeightOptimum_no_constant_isotropicPlane
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m)
    (V : Submodule K (Fin 4 → K))
    (u v : Fin 4 → K) (hu : u ∈ V) (hv : v ∈ V)
    (hu0 : u ≠ 0) (hvspan : ∀ a : K, v ≠ a • u)
    (hiso : ∀ d ∈ V, ∀ e ∈ V,
      extremalHessianPair (initialForm w m P) d e = 0) : False := by
  classical
  let L := initialForm w m P
  have hL : MvPolynomial.IsWeightedHomogeneous w L m := initialForm_isWeightedHomogeneous w m P
  have hzero (a : Fin 4 → K) (ha : a ∈ V) (b : Fin 4 → K) (hb : b ∈ V) :
      extremalHessianPair L a b = 0 := hiso a ha b hb
  obtain ⟨k,hk,hmax⟩ := extremal_exists_topWeight_pivot w u hu0
  let b := v - (v k / u k) • u
  have hb : b ∈ V := V.sub_mem hv (V.smul_mem _ hu)
  have hb0 : b ≠ 0 := by
    intro hz
    exact hvspan _ (sub_eq_zero.mp hz)
  have hbk : b k = 0 := by
    change v k - v k / u k * u k = 0
    rw [div_mul_cancel₀ _ hk, sub_self]
  obtain ⟨l,hl,hlmax⟩ := extremal_exists_topWeight_pivot w b hb0
  have hkl : k ≠ l := by
    intro he
    exact hl (he ▸ hbk)
  let a' := extremalWeightBlock w (w k) u
  let b' := extremalWeightBlock w (w l) b
  have hak : a' k = u k := by simp [a',extremalWeightBlock]
  have hbl : b' l = b l := by simp [b',extremalWeightBlock]
  have hbk' : b' k = 0 := by simp [b',extremalWeightBlock,hbk]
  have hpa : extremalHessianPair L a' a' = 0 := by
    change extremalHessianPair L (extremalWeightBlock w (w k) u)
      (extremalWeightBlock w (w k) u) = 0
    rw [extremalHessianPair_topBlocks L w m _ _ hL u u hmax hmax,
      hzero u hu u hu, map_zero]
  have hpb : extremalHessianPair L b' b' = 0 := by
    change extremalHessianPair L (extremalWeightBlock w (w l) b)
      (extremalWeightBlock w (w l) b) = 0
    rw [extremalHessianPair_topBlocks L w m _ _ hL b b hlmax hlmax,
      hzero b hb b hb, map_zero]
  have hpab : extremalHessianPair L a' b' = 0 := by
    change extremalHessianPair L (extremalWeightBlock w (w k) u)
      (extremalWeightBlock w (w l) b) = 0
    rw [extremalHessianPair_topBlocks L w m _ _ hL u b hmax hlmax,
      hzero u hu b hb, map_zero]
  let d : Fin 4 → K := fun i => (u k)⁻¹ * a' i
  let e : Fin 4 → K := fun i => (b l)⁻¹ * b' i
  have hdk : d k = 1 := by change (u k)⁻¹ * a' k = 1; rw [hak,inv_mul_cancel₀ hk]
  have hel : e l = 1 := by change (b l)⁻¹ * b' l = 1; rw [hbl,inv_mul_cancel₀ hl]
  have hek : e k = 0 := by change (b l)⁻¹ * b' k = 0; rw [hbk',mul_zero]
  have hd (i : Fin 4) (hi : w i ≠ w k) : d i = 0 := by
    simp [d,a',extremalWeightBlock,hi]
  have he (i : Fin 4) (hi : w i ≠ w l) : e i = 0 := by
    simp [e,b',extremalWeightBlock,hi]
  have hdd : extremalHessianPair L d d = 0 := by
    change extremalHessianPair L (fun i => (u k)⁻¹*a' i) (fun i => (u k)⁻¹*a' i) = 0
    rw [extremalHessianPair_scale, hpa, mul_zero, zero_mul]
  have hee : extremalHessianPair L e e = 0 := by
    change extremalHessianPair L (fun i => (b l)⁻¹*b' i) (fun i => (b l)⁻¹*b' i) = 0
    rw [extremalHessianPair_scale, hpb, mul_zero, zero_mul]
  have hde : extremalHessianPair L d e = 0 := by
    change extremalHessianPair L (fun i => (u k)⁻¹*a' i) (fun i => (b l)⁻¹*b' i) = 0
    rw [extremalHessianPair_scale, hpab, mul_zero, zero_mul]
  obtain ⟨N,hN,hNb,hNk,hNl⟩ := extremal_align_two_blocks w d e k l hkl hdk hel hek hd he
  have hcolk : (fun i => N i k) = d := funext hNk
  have hcoll : (fun i => N i l) = e := funext hNl
  have hn := globalWeightOptimum_no_zero_principalPlane P w m hw hm hcap hclock hopt N hN hNb k l hkl
  apply hn
  rw [weightedLinearSubstitution_initialForm w N hNb]
  change hessian (weightedLinearSubstitution N L) k k = 0 ∧
    hessian (weightedLinearSubstitution N L) l l = 0 ∧
    hessian (weightedLinearSubstitution N L) k l = 0
  constructor
  · rw [extremalHessianPair_chart_entry, hcolk, hdd, map_zero]
  constructor
  · rw [extremalHessianPair_chart_entry, hcoll, hee, map_zero]
  · rw [extremalHessianPair_chart_entry, hcolk, hcoll, hde, map_zero]

end
end HC4.Polynomial

#print axioms HC4.Polynomial.extremalHessianPair_topBlocks
#print axioms HC4.Polynomial.extremal_align_two_blocks
#print axioms HC4.Polynomial.globalWeightOptimum_no_constant_isotropicPlane
