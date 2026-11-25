import HC4.Polynomial.RationalCharacteristicRankTwoFrontier
import Mathlib.RingTheory.Derivation.Lie

/-!
# The rank-two characteristic normal

The source Hessian sends the right kernel to the left kernel.
After normalizing a nonzero component, this normal is invariant
under the rational kernel derivation. This is a differential
statement on the original velocity field, not a claim that the
normal is already constant over the ground field.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section MatrixAlgebra

variable {F : Type*} [Field F]

/-- Two left-kernel vectors of a matrix of rank at least two in
dimension three are proportional, in the explicit minor form. -/
theorem rankTwo_leftKernel_minors_zero
    (N : Matrix (Fin 3) (Fin 3) F) (hr : 2 ≤ N.rank)
    (b c : Fin 3 → F) (hb : b ᵥ* N = 0) (hc : c ᵥ* N = 0) :
    ∀ i j : Fin 3, b i * c j = b j * c i := by
  classical
  let M : Matrix (Fin 3) (Fin 3) F :=
    fun i j => if i = 0 then b j else if i = 1 then c j else 0
  have hM : M * N = 0 := by
    apply Matrix.ext
    intro i j
    fin_cases i
    · simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct] using congrFun hb j
    · simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct] using congrFun hc j
    · simp [M, Matrix.mul_apply]
  have hsmall := Matrix.rank_add_rank_le_card_of_mul_eq_zero hM
  rw [Fintype.card_fin] at hsmall
  intro i j
  by_contra h
  have hminor : M 0 i * M 1 j ≠ M 0 j * M 1 i := by
    simpa [M] using h
  have hh := rankTwo_rank_ge_two_of_minor M 0 1 i j hminor
  omega

/-- A self-adjoint square has a symmetric Hessian-weighted matrix.
The matrix has rank one in the remaining rank-two case. -/
theorem rankTwo_weightedSquare
    (H N : Matrix (Fin 3) (Fin 3) F)
    (hH : H.transpose = H) (hreg : H.det ≠ 0)
    (hself : N.transpose * H = H * N)
    (h3 : N ^ 3 = 0)
    (hm : ∃ a b i j : Fin 3, N a i * N b j ≠ N a j * N b i) :
    (H * (N * N)).transpose = H * (N * N) ∧
      H * (N * N) ≠ 0 ∧ (H * (N * N)).rank ≤ 1 := by
  obtain ⟨_, hs, hr, _, _⟩ := rankTwo_square_frontier N h3 hm
  have hsym : (H * (N * N)).transpose = H * (N * N) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hH, Matrix.mul_assoc,
      hself, ← Matrix.mul_assoc, hself, Matrix.mul_assoc]
  have hn : H * (N * N) ≠ 0 := by
    intro hz
    apply hs
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => H⁻¹ * M) hz
    change H⁻¹ * (H * (N * N)) = H⁻¹ * 0 at hh
    rw [Matrix.nonsing_inv_mul_cancel_left H _ (isUnit_iff_ne_zero.mpr hreg),
      Matrix.mul_zero] at hh
    exact hh
  exact ⟨hsym, hn, (Matrix.rank_mul_le_right _ _).trans hr⟩

/-- The actual Hessian carries any nonzero right kernel vector
to a nonzero left normal. -/
theorem rankTwo_hessian_leftNormal
    (H N : Matrix (Fin 3) (Fin 3) F)
    (hreg : H.det ≠ 0) (hself : N.transpose * H = H * N)
    (w : Fin 3 → F) (hw : w ≠ 0) (hk : N *ᵥ w = 0) :
    H *ᵥ w ≠ 0 ∧ (H *ᵥ w) ᵥ* N = 0 := by
  constructor
  · intro hz
    apply hw
    have hi := Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_iff_ne_zero.mpr hreg)
    apply hi
    rw [hz, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hself,
      ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]

end MatrixAlgebra

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3

/-- A derivation of the transverse fraction field is determined by
the three original coordinate values. -/
theorem rationalDerivation_eq_zero_of_X
    (D : Derivation K (E K) (E K))
    (h : ∀ i : Fin 3, D (algebraMap (B K) (E K) (X i)) = 0) :
    D = 0 := by
  have hpoly : D.compAlgebraMap (A := B K) = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    exact h i
  have hp (p : B K) : D (algebraMap (B K) (E K) p) = 0 :=
    congrArg (fun d : Derivation K (B K) (E K) => d p) hpoly
  apply Derivation.ext
  intro z
  rw [← IsFractionRing.mk'_num_den' (B K) z, Derivation.leibniz_div]
  simp [hp]

/-- Localized transverse partials commute on the full fraction
field, by applying the derivation commutator to the coordinates. -/
theorem rationalCharacteristicPartial_comm
    (i j : Fin 3) (z : E K) :
    rationalCharacteristicPartial i (rationalCharacteristicPartial j z) =
      rationalCharacteristicPartial j (rationalCharacteristicPartial i z) := by
  let Di := rationalCharacteristicPartial (K := K) i
  let Dj := rationalCharacteristicPartial (K := K) j
  have hc : ⁅Di, Dj⁆ = 0 := by
    apply rationalDerivation_eq_zero_of_X
    intro k
    rw [Derivation.commutator_apply]
    have hD (l : Fin 3) :
        rationalCharacteristicPartial l (algebraMap (B K) (E K) (X k)) =
          if k = l then 1 else 0 := by
      rw [rationalCharacteristicPartial_algebraMap]
      by_cases h : k = l
      · subst k; simp
      · simp [h, pderiv_X_of_ne h]
    dsimp only [Di, Dj]
    rw [hD j, hD i]
    split_ifs <;> simp
  have h := congrArg (fun D : Derivation K (E K) (E K) => D z) hc
  change Di (Dj z) - Dj (Di z) = 0 at h
  exact sub_eq_zero.mp h

/-- Differentiating the kernel equation along an original coordinate
shows how the Jacobian evolves along its right-kernel direction. -/
theorem rankTwo_kernel_derivativeJacobian
    (V : I → E K) (w : Fin 3 → E K)
    (hw : rationalCharacteristicJacobian V *ᵥ w = 0)
    (i j : Fin 3) :
    rankTwo_directionalDerivation w (rationalCharacteristicJacobian V i j) =
      -∑ k : Fin 3, rationalCharacteristicJacobian V i k *
        rationalCharacteristicPartial j (w k) := by
  classical
  let N := rationalCharacteristicJacobian V
  let D := rationalCharacteristicPartial (K := K) j
  have hz := congrFun hw i
  change (∑ k : Fin 3, N i k * w k) = 0 at hz
  have h := congrArg D hz
  change D (∑ k : Fin 3, N i k * w k) = D 0 at h
  simp only [map_sum, map_zero, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib] at h
  rw [rankTwo_directionalDerivation_apply]
  change (∑ k : Fin 3, w k * rationalCharacteristicPartial k
    (rationalCharacteristicPartial j (V (.inr i)))) = _
  have he : (∑ k : Fin 3, w k * rationalCharacteristicPartial k
      (rationalCharacteristicPartial j (V (.inr i)))) =
      ∑ k : Fin 3, w k * D (N i k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [rationalCharacteristicPartial_comm k j]
    rfl
  rw [he]
  change (∑ k : Fin 3, w k * D (N i k)) =
    -(∑ k : Fin 3, N i k * D (w k))
  linear_combination h

/-- Every left normal, after differentiation in a kernel direction,
is still a left normal. -/
theorem rankTwo_leftNormal_derivative_kernel
    (V : I → E K) (w b : Fin 3 → E K)
    (hw : rationalCharacteristicJacobian V *ᵥ w = 0)
    (hb : b ᵥ* rationalCharacteristicJacobian V = 0) :
    (fun i => rankTwo_directionalDerivation w (b i)) ᵥ*
      rationalCharacteristicJacobian V = 0 := by
  classical
  let N := rationalCharacteristicJacobian V
  let D := rankTwo_directionalDerivation w
  funext j
  have hbj (k : Fin 3) : (∑ i : Fin 3, b i * N i k) = 0 := congrFun hb k
  have h := congrArg D (hbj j)
  change D (∑ i : Fin 3, b i * N i j) = D 0 at h
  simp only [map_sum, map_zero, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib] at h
  have hz : (∑ i : Fin 3, b i * D (N i j)) = 0 := by
    have he (i : Fin 3) : D (N i j) =
        -∑ k : Fin 3, N i k * rationalCharacteristicPartial j (w k) :=
      rankTwo_kernel_derivativeJacobian V w hw i j
    calc
      (∑ i : Fin 3, b i * D (N i j)) =
          -(∑ i : Fin 3, ∑ k : Fin 3,
            b i * (N i k * rationalCharacteristicPartial j (w k))) := by
        simp only [he, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
      _ = 0 := by
        rw [Finset.sum_comm]
        simp_rw [← mul_assoc, ← Finset.sum_mul, hbj, zero_mul]
        simp
  rw [hz, zero_add] at h
  change (∑ i : Fin 3, D (b i) * N i j) = 0
  simpa only [mul_comm] using h

/-- The normalized left normal is invariant along the velocity
kernel derivation. This does not yet make it a ground-field vector. -/
theorem rankTwo_normalizedLeftNormal_invariant
    (V : I → E K) (w b : Fin 3 → E K)
    (hr : 2 ≤ (rationalCharacteristicJacobian V).rank)
    (hw : rationalCharacteristicJacobian V *ᵥ w = 0)
    (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (k : Fin 3) (hk : b k = 1) :
    ∀ i : Fin 3, rankTwo_directionalDerivation w (b i) = 0 := by
  let D := rankTwo_directionalDerivation w
  let c : Fin 3 → E K := fun i => D (b i)
  have hc : c ᵥ* rationalCharacteristicJacobian V = 0 :=
    rankTwo_leftNormal_derivative_kernel V w b hw hb
  have hck : c k = 0 := by
    change D (b k) = 0
    rw [hk, D.map_one_eq_zero]
  intro i
  have hh := rankTwo_leftKernel_minors_zero _ hr b c hb hc k i
  rw [hk, hck, one_mul, mul_zero] at hh
  exact hh

end
end HC4.Polynomial.RankThreeCubic
