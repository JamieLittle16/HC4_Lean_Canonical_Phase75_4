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
    _ = M *ᵥ (P *ᵥ (A *ᵥ w)) := by
      rw [← hMP, ← Matrix.mulVec_mulVec]
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
    change (N *ᵥ u) i = (M * (rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) (E K))) i 0 at he
    have hj (k : Fin 3) : (rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) (E K)) k 0 = 0 := by
      fin_cases k <;> rfl
    have hz : (M * (rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) (E K))) i 0 = 0 := by
      rw [Matrix.mul_apply]
      simp only [hj, mul_zero, Finset.sum_const_zero]
    exact he.trans hz
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

/-- If the direction is invariant along itself, differentiation of
coefficients of an actual polynomial line equals differentiation in
the line parameter. No rational evaluation at poles is involved. -/
theorem rankTwo_lineEval_coeffDeriv_eq_derivative
    (w : Fin 3 → E K)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (p : B K) :
    let e := lineEval (K := K) (fun i => algebraMap (B K) (E K) (X i)) w
    coeffDeriv (rankTwo_directionalDerivation w) (e p) =
      _root_.Polynomial.derivative (e p) := by
  let D := rankTwo_directionalDerivation w
  let e := lineEval (K := K) (fun i => algebraMap (B K) (E K) (X i)) w
  change coeffDeriv D (e p) = _root_.Polynomial.derivative (e p)
  have hx (i : Fin 3) : coeffDeriv D (e (X i)) =
      _root_.Polynomial.derivative (e (X i)) := by
    have he : e (X i) = _root_.Polynomial.C (algebraMap (B K) (E K) (X i)) +
        _root_.Polynomial.C (w i) * _root_.Polynomial.X := by
      dsimp only [e, lineEval]
      rw [MvPolynomial.aeval_X]
    rw [he]
    have hd (i : Fin 3) : D (algebraMap (B K) (E K) (X i)) = w i :=
      rankTwo_directionalDerivation_X w i
    have hzero (i : Fin 3) : D (w i) = 0 := hw i
    simp only [map_add, coeffDeriv_C, Derivation.leibniz, smul_eq_mul,
      coeffDeriv_X, hd, hzero, map_zero, mul_zero, zero_mul, add_zero,
      _root_.Polynomial.derivative_add, _root_.Polynomial.derivative_C,
      _root_.Polynomial.derivative_C_mul, _root_.Polynomial.derivative_X,
      mul_one, zero_add]
  induction p using MvPolynomial.induction_on with
  | C c =>
    have he : e (MvPolynomial.C c) = _root_.Polynomial.C (algebraMap K (E K) c) := by
      simp [e, lineEval, IsScalarTower.algebraMap_apply K (E K)
        (_root_.Polynomial (E K)), _root_.Polynomial.algebraMap_eq]
    rw [he, coeffDeriv_C, _root_.Polynomial.derivative_C, D.map_algebraMap, map_zero]
  | add p q hp hq =>
    rw [map_add, map_add, _root_.Polynomial.derivative_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      _root_.Polynomial.derivative_mul, hp, hx]
    ring

/-- A coefficient-transport polynomial is uniquely determined by
its constant coefficient. In characteristic zero the recurrence
forces all higher coefficients to vanish if the constant is zero. -/
theorem rankTwo_transportPolynomial_eq_zero
    (D : Derivation K (E K) (E K)) (p : _root_.Polynomial (E K))
    (h : coeffDeriv D p = _root_.Polynomial.derivative p)
    (h0 : p.coeff 0 = 0) : p = 0 := by
  have hz (n : ℕ) : p.coeff n = 0 := by
    induction n with
    | zero => exact h0
    | succ n ih =>
      have he := congrArg (fun q : _root_.Polynomial (E K) => q.coeff n) h
      change (coeffDeriv D p).coeff n = (_root_.Polynomial.derivative p).coeff n at he
      rw [coeff_coeffDeriv, _root_.Polynomial.coeff_derivative, ih, map_zero] at he
      have hn : ((n + 1 : ℕ) : E K) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      rcases mul_eq_zero.mp he.symm with h | h
      · first | exact h | exact (hn h).elim
      · first | exact h | exact (hn h).elim
  apply _root_.Polynomial.ext
  intro n
  rw [hz, _root_.Polynomial.coeff_zero]

/-- Actual rational invariants are constant on the entire generic
straight line, in a denominator-cleared polynomial identity.
The denominator survives because its time-zero coefficient is nonzero. -/
theorem rankTwo_invariant_lineEval
    (w : Fin 3 → E K)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (z : E K) (hz : rankTwo_directionalDerivation w z = 0)
    (p q : B K) (hq : q ≠ 0)
    (hrep : algebraMap (B K) (E K) p / algebraMap (B K) (E K) q = z) :
    let e := lineEval (K := K) (fun i => algebraMap (B K) (E K) (X i)) w
    e q ≠ 0 ∧ e p = _root_.Polynomial.C z * e q := by
  let g : B K →+* E K := algebraMap (B K) (E K)
  let x : Fin 3 → E K := fun i => g (X i)
  let e := lineEval (K := K) x w
  let D := rankTwo_directionalDerivation w
  have hcoeff (b : B K) : (e b).coeff 0 = g b := by
    change (lineEval x w b).coeff 0 = g b
    rw [cubic_lineEval_coeff_zero]
    have he : (MvPolynomial.aeval x : B K →ₐ[K] E K).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro r
        calc
          MvPolynomial.aeval x (MvPolynomial.C r) = algebraMap K (E K) r :=
            (MvPolynomial.aeval x).commutes r
          _ = g (MvPolynomial.C r) :=
            ((IsScalarTower.toAlgHom K (B K) (E K)).commutes r).symm
      · intro i
        exact MvPolynomial.aeval_X x i
    exact RingHom.congr_fun he b
  have hqg : g q ≠ 0 := by
    intro h
    apply hq
    apply IsFractionRing.injective (B K) (E K)
    simpa only [map_zero] using h
  have hmul : g p = z * g q := by
    rw [← hrep, div_mul_cancel₀ _ hqg]
  have hD (b : B K) : coeffDeriv D (e b) = _root_.Polynomial.derivative (e b) :=
    rankTwo_lineEval_coeffDeriv_eq_derivative w hw b
  refine ⟨?_, ?_⟩
  · intro h
    apply hqg
    rw [← hcoeff q, h, _root_.Polynomial.coeff_zero]
  · apply sub_eq_zero.mp
    apply rankTwo_transportPolynomial_eq_zero D
    · change coeffDeriv D (e p - _root_.Polynomial.C z * e q) =
        _root_.Polynomial.derivative (e p - _root_.Polynomial.C z * e q)
      have hz' : D z = 0 := hz
      simp only [map_sub, Derivation.leibniz, smul_eq_mul, coeffDeriv_C,
        hz', map_zero, mul_zero, add_zero, hD, _root_.Polynomial.derivative_sub,
        _root_.Polynomial.derivative_C_mul]
    · change (e p - _root_.Polynomial.C z * e q).coeff 0 = 0
      rw [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_C_mul,
        hcoeff, hcoeff, hmul, sub_self]

end
end HC4.Polynomial.RankThreeCubic
