import HC4.Polynomial.WeightedComplementaryInitialForm
import HC4.Polynomial.RankThreeCubicPrincipalAdjugateDirection

/-!
# The complementary kernel lifts to the full leading Hessian

If a symmetric singular four-dimensional matrix has a singular
three-dimensional complementary principal block, each column of
the latter's adjugate, extended by zero in the distinguished
coordinate, is killed by the full matrix.

The proof uses an actual nonzero full kernel vector. If its
distinguished coordinate is nonzero, symmetry gives the mixed
orthogonality directly. Otherwise its transverse part is a
nonzero kernel of the complementary block, and a surviving
principal cofactor compares it with every adjugate column.

No division, regular full minor, or constant kernel hypothesis
is used. The adjugate-zero branch is retained explicitly.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

private abbrev I := Unit ⊕ Fin 3

section Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Every complementary adjugate column lifts to a full kernel
vector on the same matrix, not on a replacement Hessian. -/
theorem singular_complementary_adjugate_lifts
    (A : Matrix I I R) (hs : A.IsSymm) (hd : A.det = 0)
    (hB : (A.submatrix Sum.inr Sum.inr).det = 0) :
    ∀ j : Fin 3, A *ᵥ
      (Sum.elim (fun _ : Unit => (0 : R))
        (fun i : Fin 3 => (A.submatrix Sum.inr Sum.inr).adjugate i j)) = 0 := by
  classical
  let B : Matrix (Fin 3) (Fin 3) R := A.submatrix Sum.inr Sum.inr
  let b : Fin 3 → R := fun i => A (.inl ()) (.inr i)
  have hBs : B.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hs.apply (.inr i) (.inr j)
  have hBA : B * B.adjugate = 0 := by
    rw [Matrix.mul_adjugate, show B.det = 0 from hB, zero_smul]
  have hBker (j : Fin 3) : B *ᵥ (fun i => B.adjugate i j) = 0 := by
    funext i
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M i j) hBA
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  let v : Fin 3 → R := fun i => u (.inr i)
  have hul : u ᵥ* A = 0 := by
    rw [← Matrix.mulVec_transpose, hs, hu]
  have hrow (j : Fin 3) :
      A *ᵥ (Sum.elim (fun _ : Unit => (0 : R))
        (fun i : Fin 3 => B.adjugate i j)) =
      Sum.elim (fun _ : Unit => b ⬝ᵥ (fun i => B.adjugate i j))
        (fun _ : Fin 3 => 0) := by
    funext i
    cases i with
    | inl i =>
      cases i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, b]
    | inr i =>
      have he := congrFun (hBker j) i
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, B] using he
  intro j
  rw [hrow j]
  have hmixed : b ⬝ᵥ (fun i => B.adjugate i j) = 0 := by
    by_cases h0 : u (.inl ()) = 0
    · have hv : v ≠ 0 := by
        intro hz
        apply hu0
        funext i
        cases i with
        | inl a => cases a; exact h0
        | inr i => exact congrFun hz i
      have hvker : B *ᵥ v = 0 := by
        funext i
        have he := congrFun hu (.inr i)
        simpa [B, v, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h0] using he
      have hbv : b ⬝ᵥ v = 0 := by
        have he := congrFun hu (.inl ())
        simpa [b, v, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h0] using he
      by_cases hz : B.adjugate = 0
      · simp [hz, dotProduct]
      · obtain ⟨k, hk⟩ := singular_symmetric_exists_principalCofactor B hBs hB hz
        have hvk : v k ≠ 0 := by
          intro h
          exact hk (adjugate_entry_zero_of_nonzero_kernel_coordinate_zero B v hvker hv k k h)
        let z : Fin 3 → R := fun i => B.adjugate i j
        have hzker : B *ᵥ z = 0 := hBker j
        have hp := principalCofactor_kernelVector_adjugate_proportional B v hvker hB k hk
        have hq := principalCofactor_kernelVector_adjugate_proportional B z hzker hB k hk
        have hrel (i : Fin 3) : v k * z i = z k * v i := by
          apply mul_left_cancel₀ hk
          calc
            B.adjugate k k * (v k * z i) =
                v k * (B.adjugate k k * z i) := by ring
            _ = v k * (B.adjugate i k * z k) := by rw [hq i]
            _ = z k * (B.adjugate i k * v k) := by ring
            _ = z k * (B.adjugate k k * v i) := by rw [hp i]
            _ = B.adjugate k k * (z k * v i) := by ring
        change b ⬝ᵥ z = 0
        suffices he : v k * (b ⬝ᵥ z) = 0 by
          exact (mul_eq_zero.mp he).resolve_left hvk
        calc
          v k * (b ⬝ᵥ z) = ∑ i : Fin 3, b i * (v k * z i) := by
            rw [dotProduct, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = ∑ i : Fin 3, b i * (z k * v i) := by simp only [hrel]
          _ = z k * (b ⬝ᵥ v) := by
            rw [dotProduct, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = 0 := by rw [hbv, mul_zero]
    · let z : I → R := Sum.elim (fun _ : Unit => 0) (fun i : Fin 3 => B.adjugate i j)
      have he := Matrix.dotProduct_mulVec u A z
      rw [hul, zero_dotProduct] at he
      change u ⬝ᵥ (A *ᵥ z) = 0 at he
      change u ⬝ᵥ (A *ᵥ (Sum.elim (fun _ : Unit => (0 : R))
        (fun i : Fin 3 => B.adjugate i j))) = 0 at he
      rw [hrow j] at he
      have hh : u (.inl ()) * (b ⬝ᵥ (fun i => B.adjugate i j)) = 0 := by
        simpa [dotProduct, Fintype.sum_sum_type] using he
      exact (mul_eq_zero.mp hh).resolve_left h0
  rw [hmixed]
  funext i
  cases i <;> rfl

end Matrix

variable {K : Type*} [Field K] [CharZero K]
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

set_option maxHeartbeats 4000000 in
/-- The genuine maximal weighted layer in the determinant-one
chart has a singular complementary Hessian, whose adjugate
columns lift to kernels of the entire (permuted) leading Hessian.
This records the mixed-derivative equations, not just its minor. -/
theorem weightedLeading_exists_complementaryKernel_chart
    (w : I → ℤ) (m : ℤ) (P : S K)
    (hcap : IsWeightLE w m P)
    (hW : (Fintype.card I : ℤ) * m - 2 * (∑ i : I, w i) ≠ 0)
    {δ : K} (hdet : hessianDeterminant P = MvPolynomial.C δ) :
    ∃ (M : Matrix I I K) (k : I),
      M.det = 1 ∧
      (∀ i j, w i ≠ w j → M i j = 0) ∧
      let P' := weightedLinearSubstitution M P
      let L' := initialForm w m P'
      let e : I ≃ I := Equiv.swap (.inl ()) k
      let A := (hessian L').submatrix e e
      let B := A.submatrix Sum.inr Sum.inr
      IsWeightLE w m P' ∧ hessianDeterminant P' = MvPolynomial.C δ ∧
      (∀ i, (hessian L').adjugate i k = 0) ∧ B.det = 0 ∧
      ∀ j : Fin 3, A *ᵥ (Sum.elim (fun _ : Unit => (0 : S K))
        (fun i : Fin 3 => B.adjugate i j)) = 0 := by
  classical
  obtain ⟨M, k, hM, hw, hcap', hdet', hcol, hB⟩ :=
    weightedLeading_exists_actual_complementaryHessian w m P hcap hW hdet
  refine ⟨M, k, hM, hw, hcap', hdet', hcol, hB, ?_⟩
  let P' := weightedLinearSubstitution M P
  let L' := initialForm w m P'
  let e : I ≃ I := Equiv.swap (.inl ()) k
  let A := (hessian L').submatrix e e
  have hs : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change pderiv (e i) (pderiv (e j) L') = pderiv (e j) (pderiv (e i) L')
    exact HC4.Newton.pderiv_comm_backport _ _ _
  have hdL : (hessian L').det = 0 := by
    change hessianDeterminant (initialForm w m P') = 0
    rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m P' hcap', hdet']
    exact initialForm_eq_zero_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_C w δ) _ hW
  have hdA : A.det = 0 := by
    change ((hessian L').submatrix e e).det = 0
    rw [Matrix.det_submatrix_equiv_self, hdL]
  exact singular_complementary_adjugate_lifts A hs hdA hB

end
end HC4.Polynomial.RankThreeCubic

#print axioms HC4.Polynomial.RankThreeCubic.weightedLeading_exists_complementaryKernel_chart
