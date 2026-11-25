import HC4.Polynomial.RationalCharacteristicRankTwoNormal

/-!
# A source-derived dual line in the remaining rank-two case

A column of N² is in the image and kernel of N. Its Hessian
image is a nonzero left normal. Normalize both by the same
component of that normal. Along the resulting derivation the
original transverse gradients have constant first derivative
and zero second derivative; the normal and velocities are
invariant. The direction is null for the Hessian.

The dual Euler potential also has zero second derivative.
These are identities in the actual transverse fraction field,
not an assumption of a polynomial inverse gradient map.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- Derivatives of the actual reference gradient are its Hessian
applied to the direction. -/
theorem rankTwo_referenceGradient_derivative
    (f : B K) (w : Fin 3 → E K) (i : Fin 3) :
    rankTwo_directionalDerivation w
      (algebraMap (B K) (E K) (pderiv i f)) =
    ((hessian f).map (algebraMap (B K) (E K)) *ᵥ w) i := by
  rw [rankTwo_directionalDerivation_apply]
  simp only [rationalCharacteristicPartial_algebraMap, Matrix.mulVec, dotProduct,
    Matrix.map_apply, hessian_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The normalized kernel direction can be chosen in the image of N,
so it is orthogonal to its own Hessian image. -/
theorem rankTwo_exists_normalizedDualDirection
    (a : K) (L : S K) (V : I → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (w b : Fin 3 → E K) (k : Fin 3),
      b k = 1 ∧
      rationalCharacteristicJacobian V *ᵥ w = 0 ∧
      rationalCharacteristicHessian a L *ᵥ w = b ∧
      b ᵥ* rationalCharacteristicJacobian V = 0 ∧
      b ⬝ᵥ w = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (b i) = 0) ∧
      (∀ i : Fin 3, rankTwo_directionalDerivation w (V (.inr i)) = 0) := by
  classical
  let N := rationalCharacteristicJacobian V
  let H := rationalCharacteristicHessian a L
  have h3 : N ^ 3 = 0 :=
    rationalCharacteristicJacobian_cube_eq_zero a L V hV hreg (fun i => hgrad (.inr i))
  have hself : N.transpose * H = H * N :=
    rationalCharacteristicJacobian_selfAdjoint a L V hV (fun i => hgrad (.inr i))
  have hminor : ∃ a b i j : Fin 3, N a i * N b j ≠ N a j * N b i := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h ⟨a, i, b, j, hz⟩
  obtain ⟨hr, hs, _, hl, _⟩ := rankTwo_square_frontier N h3 hminor
  have hex : ∃ i j : Fin 3, (N * N) i j ≠ 0 := by
    by_contra h
    apply hs
    apply Matrix.ext
    intro i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hex
  let u : Fin 3 → E K := fun k => N k j
  let w₀ : Fin 3 → E K := N *ᵥ u
  have hwcol (k : Fin 3) : w₀ k = (N * N) k j := rfl
  have hw₀ : w₀ ≠ 0 := by
    intro hz
    exact hij ((hwcol i).symm.trans (congrFun hz i))
  have hk₀ : N *ᵥ w₀ = 0 := by
    funext k
    change (∑ l : Fin 3, N k l * w₀ l) = 0
    simp only [hwcol]
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (E K) => M k j) hl
  let b₀ := H *ᵥ w₀
  obtain ⟨hb₀, hleft₀⟩ := rankTwo_hessian_leftNormal H N
    (rationalCharacteristicHessian_det_ne_zero a L hreg) hself w₀ hw₀ hk₀
  have hexk : ∃ k : Fin 3, b₀ k ≠ 0 := by
    by_contra h
    apply hb₀
    funext k
    by_contra hk
    exact h ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hexk
  let w : Fin 3 → E K := (b₀ k)⁻¹ • w₀
  let b : Fin 3 → E K := (b₀ k)⁻¹ • b₀
  have hb : b k = 1 := by
    change (b₀ k)⁻¹ * b₀ k = 1
    exact inv_mul_cancel₀ hk
  have hw : N *ᵥ w = 0 := by
    rw [show w = (b₀ k)⁻¹ • w₀ from rfl, Matrix.mulVec_smul, hk₀, smul_zero]
  have hh : H *ᵥ w = b := by
    rw [show w = (b₀ k)⁻¹ • w₀ from rfl, Matrix.mulVec_smul]
  have hleft : b ᵥ* N = 0 := by
    rw [show b = (b₀ k)⁻¹ • b₀ from rfl, Matrix.smul_vecMul, hleft₀, smul_zero]
  have hnull : b ⬝ᵥ w = 0 := by
    have he : w = N *ᵥ ((b₀ k)⁻¹ • u) := by
      rw [Matrix.mulVec_smul]
    rw [he, Matrix.dotProduct_mulVec, hleft]
    simp [dotProduct]
  refine ⟨w, b, k, hb, hw, hh, hleft, hnull,
    rankTwo_normalizedLeftNormal_invariant V w b hr hw hleft k hb, ?_⟩
  intro i
  rw [rankTwo_directionalDerivation_apply]
  have he := congrFun hw i
  change (∑ j : Fin 3, N i j * w j) = 0 at he
  simpa only [N, rationalCharacteristicJacobian, mul_comm] using he

/-- A normalized dual direction makes the actual transverse gradient
affine under the derivation, and makes the Euler potential affine
as well. The null identity kills its second derivative. -/
theorem rankTwo_dualEuler_affine
    (f : B K) (w b : Fin 3 → E K)
    (hh : (hessian f).map (algebraMap (B K) (E K)) *ᵥ w = b)
    (hb : ∀ i, rankTwo_directionalDerivation w (b i) = 0)
    (hn : b ⬝ᵥ w = 0) :
    (∀ i, rankTwo_directionalDerivation w
      (algebraMap (B K) (E K) (pderiv i f)) = b i) ∧
    (∀ i, rankTwo_directionalDerivation w
      (rankTwo_directionalDerivation w
        (algebraMap (B K) (E K) (pderiv i f))) = 0) ∧
    rankTwo_directionalDerivation w
      (rankTwo_directionalDerivation w
        (algebraMap (B K) (E K) (transverseEuler f - f))) = 0 := by
  classical
  let D := rankTwo_directionalDerivation w
  let e := algebraMap (B K) (E K)
  have hg (i : Fin 3) : D (e (pderiv i f)) = b i := by
    rw [show D (e (pderiv i f)) =
      ((hessian f).map e *ᵥ w) i from rankTwo_referenceGradient_derivative f w i, hh]
  refine ⟨hg, ?_, ?_⟩
  · intro i
    change D (D (e (pderiv i f))) = 0
    rw [hg, hb]
  · have hEuler : D (e (transverseEuler f - f)) =
        ∑ i : Fin 3, e (X i) * b i := by
      rw [rankTwo_directionalDerivation_apply]
      simp only [rationalCharacteristicPartial_algebraMap,
        ← rankOne_radialHessian_eq_eulerGradient, map_sum, map_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have he : b j = ∑ i : Fin 3, e (hessian f j i) * w i := by
        exact (congrFun hh j).symm
      rw [he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hs : hessian f i j = hessian f j i := by
        simp only [hessian_apply]
        rw [HC4.Newton.pderiv_comm_backport]
      rw [hs]
      ring
    change D (D (e (transverseEuler f - f))) = 0
    rw [hEuler, map_sum]
    have he (i : Fin 3) : D (e (X i)) = w i :=
      rankTwo_directionalDerivation_X w i
    simp only [Derivation.leibniz, smul_eq_mul, hb, he, mul_zero, zero_add]
    exact hn

/-- The dual affine identities are obtained from the actual anchored
source, without a separate existence or regularity premise on w. -/
theorem rankTwo_source_dualEuler_affine
    (a : K) (L : S K) (V : I → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (w b : Fin 3 → E K) (k : Fin 3), b k = 1 ∧
      b ᵥ* rationalCharacteristicJacobian V = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (b i) = 0) ∧
      (∀ i : Fin 3, rankTwo_directionalDerivation w (V (.inr i)) = 0) ∧
      (∀ i : Fin 3, rankTwo_directionalDerivation w
        (algebraMap (B K) (E K) (pderiv i (referenceSlice a L))) = b i) ∧
      rankTwo_directionalDerivation w
        (rankTwo_directionalDerivation w
          (algebraMap (B K) (E K)
            (transverseEuler (referenceSlice a L) - referenceSlice a L))) = 0 := by
  obtain ⟨w, b, k, hk, _, hh, hl, hn, hb, hv⟩ :=
    rankTwo_exists_normalizedDualDirection a L V hV hreg hgrad hm
  rw [rationalCharacteristicHessian_eq_slice_hessian] at hh
  obtain ⟨hg, _, he⟩ := rankTwo_dualEuler_affine (referenceSlice a L) w b hh hb hn
  exact ⟨w, b, k, hk, hl, hb, hv, hg, he⟩

end
end HC4.Polynomial.RankThreeCubic
