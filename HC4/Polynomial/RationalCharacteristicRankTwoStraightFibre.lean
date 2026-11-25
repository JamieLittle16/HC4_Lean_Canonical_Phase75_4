import HC4.Polynomial.RationalCharacteristicRankTwoTensorTransport

/-!
# Straightness of the rank-two velocity fibres

The transported tensor vanishing kills the acceleration modulo
the one-dimensional velocity kernel. Normalize a nonzero original
coordinate of the direction to one. The acceleration then vanishes
identically. All identities are over the original fraction field.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Algebra

variable {F : Type*} [Field F]

/-- Two right-kernel vectors are proportional, by the existing
left-kernel lemma applied to the transpose. -/
theorem rankTwo_rightKernel_minors_zero
    (N : Matrix (Fin 3) (Fin 3) F) (hr : 2 ≤ N.rank)
    (w z : Fin 3 → F) (hw : N *ᵥ w = 0) (hz : N *ᵥ z = 0) :
    ∀ i j : Fin 3, w i * z j = w j * z i := by
  have hr' : 2 ≤ N.transpose.rank := by
    rw [Matrix.rank_transpose]
    exact hr
  apply rankTwo_leftKernel_minors_zero N.transpose hr' w z
  · rw [← Matrix.mulVec_transpose, Matrix.transpose_transpose, hw]
  · rw [← Matrix.mulVec_transpose, Matrix.transpose_transpose, hz]

/-- A zero first column after frame transport is a zero product
with the original first frame vector. -/
theorem rankTwo_frame_firstColumn_zero
    (M P A : Matrix (Fin 3) (Fin 3) F) (hMP : M * P = 1)
    (h : ∀ i : Fin 3, (P * A * M) i 0 = 0) :
    A *ᵥ (fun k => M k 0) = 0 := by
  let w : Fin 3 → F := fun k => M k 0
  have he : P *ᵥ (A *ᵥ w) = 0 := by
    rw [Matrix.mulVec_mulVec]
    funext i
    exact h i
  calc
    A *ᵥ w = (1 : Matrix (Fin 3) (Fin 3) F) *ᵥ (A *ᵥ w) := by
      rw [Matrix.one_mulVec]
    _ = M *ᵥ (P *ᵥ (A *ᵥ w)) := by rw [Matrix.mulVec_mulVec, hMP]
    _ = 0 := by rw [he, Matrix.mulVec_zero]

end Algebra

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

theorem rankTwo_directionalDerivation_scale
    (s : E K) (w : Fin 3 → E K) (z : E K) :
    rankTwo_directionalDerivation (s • w) z =
      s * rankTwo_directionalDerivation w z := by
  rw [rankTwo_directionalDerivation_apply, rankTwo_directionalDerivation_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (s * w i) * rationalCharacteristicPartial i z =
    s * (w i * rationalCharacteristicPartial i z)
  ring

/-- Differentiating the zero kernel product gives the acceleration
in the kernel once the transported second derivative vanishes. -/
theorem rankTwo_acceleration_in_kernel
    (V : I → E K) (w : Fin 3 → E K)
    (hw : rationalCharacteristicJacobian V *ᵥ w = 0)
    (hzero : rankTwo_matrixDeriv (rankTwo_directionalDerivation w)
      (rationalCharacteristicJacobian V) *ᵥ w = 0) :
    rationalCharacteristicJacobian V *ᵥ
      (fun i => rankTwo_directionalDerivation w (w i)) = 0 := by
  classical
  let N := rationalCharacteristicJacobian V
  let D := rankTwo_directionalDerivation w
  funext i
  have he := congrArg D (congrFun hw i)
  change D (∑ j : Fin 3, N i j * w j) = D 0 at he
  simp only [map_sum, map_zero, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib] at he
  have hz := congrFun hzero i
  change (∑ j : Fin 3, D (N i j) * w j) = 0 at hz
  have hz' : (∑ j : Fin 3, w j * D (N i j)) = 0 := by
    simpa only [mul_comm] using hz
  rw [hz', add_zero] at he
  exact he

set_option maxHeartbeats 2000000 in
/-- The actual source admits a normalized straight velocity-kernel
direction. No separate straightness or rational inverse premise. -/
theorem rankTwo_source_straightDirection
    (a : K) (L : S K) (V : I → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (w : Fin 3 → E K) (k : Fin 3),
      w k = 1 ∧ rationalCharacteristicJacobian V *ᵥ w = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (w i) = 0) ∧
      (∀ z ∈ IntermediateField.adjoin K (Set.range (fun i : Fin 3 => V (.inr i))),
        rankTwo_directionalDerivation w z = 0) := by
  classical
  let N := rationalCharacteristicJacobian V
  obtain ⟨M, P, hd, hMP, hPM, hNM, hcol, _⟩ :=
    rankTwo_source_frameTensor a L V hV hreg hgrad hm
  let u : Fin 3 → E K := fun k => M k 0
  have hu0 : u ≠ 0 := by
    intro h
    apply hd
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    exact congrFun h i
  have hu : N *ᵥ u = 0 := by
    funext i
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (E K) => A i 0) hNM
    change (N *ᵥ u) i = (M * rankTwo_jordanBlock) i 0 at he
    have hj (k : Fin 3) : (rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) (E K)) k 0 = 0 := by
      fin_cases k <;> rfl
    rw [Matrix.mul_apply] at he
    simpa only [hj, mul_zero, Finset.sum_const_zero, Pi.zero_apply] using he
  have hzero : rankTwo_matrixDeriv (rankTwo_directionalDerivation u) N *ᵥ u = 0 :=
    rankTwo_frame_firstColumn_zero M P _ hMP hcol
  have hex : ∃ k : Fin 3, u k ≠ 0 := by
    by_contra h
    apply hu0
    funext k
    by_contra hk
    exact h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hex
  let s := (u k)⁻¹
  let w : Fin 3 → E K := s • u
  have hwk : w k = 1 := inv_mul_cancel₀ hk
  have hw : N *ᵥ w = 0 := by
    change N *ᵥ (s • u) = 0
    rw [Matrix.mulVec_smul, hu, smul_zero]
  have hscale : rankTwo_matrixDeriv (rankTwo_directionalDerivation w) N =
      s • rankTwo_matrixDeriv (rankTwo_directionalDerivation u) N := by
    apply Matrix.ext
    intro i j
    exact rankTwo_directionalDerivation_scale s u (N i j)
  have hz : rankTwo_matrixDeriv (rankTwo_directionalDerivation w) N *ᵥ w = 0 := by
    rw [hscale, show w = s • u from rfl, Matrix.smul_mulVec,
      Matrix.mulVec_smul, hzero, smul_zero, smul_zero]
  have hacc := rankTwo_acceleration_in_kernel V w hw hz
  have hr : 2 ≤ N.rank := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h (rankTwo_rank_ge_two_of_minor N a i b j hz)
  let z : Fin 3 → E K := fun i => rankTwo_directionalDerivation w (w i)
  have hzk : z k = 0 := by
    change rankTwo_directionalDerivation w (w k) = 0
    rw [hwk, Derivation.map_one_eq_zero]
  refine ⟨w, k, hwk, hw, ?_, ?_⟩
  · intro i
    have he := rankTwo_rightKernel_minors_zero N hr w z hw hacc k i
    rw [hwk, hzk, one_mul, mul_zero] at he
    exact he
  · intro z hz
    apply rationalDerivation_zero_of_mem_adjoin (rankTwo_directionalDerivation w) _ _ z hz
    rintro x ⟨i, rfl⟩
    rw [rankTwo_directionalDerivation_apply]
    have he := congrFun hw i
    change (∑ j : Fin 3, N i j * w j) = 0 at he
    simpa only [N, rationalCharacteristicJacobian, mul_comm] using he

end
end HC4.Polynomial.RankThreeCubic
