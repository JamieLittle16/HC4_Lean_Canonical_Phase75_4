import HC4.Polynomial.RationalCharacteristicRankTwoFrobeniusTensor

/-!
# The rational Jordan frame and differentiated source identities

The Jordan frame is built over the original field using a cyclic
vector, without algebraic closure. The differentiated source
identities are derived before any change of frame; the latter is
a pointwise tensor transformation, not differentiation of a
variable similarity matrix.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Frame

variable {F : Type*} [Field F]

private abbrev Mat (F : Type*) := Matrix (Fin 3) (Fin 3) F

/-- The cyclic frame with columns N²u, Nu, u is invertible whenever
N³=0 and N²u is nonzero. -/
theorem rankTwo_exists_jordanFrame
    (N : Mat F) (h3 : N * (N * N) = 0) (h2 : N * N ≠ 0) :
    ∃ M P : Mat F, M.det ≠ 0 ∧ M * P = 1 ∧ P * M = 1 ∧
      N * M = M * rankTwo_jordanBlock := by
  classical
  have he : ∃ i j : Fin 3, (N * N) i j ≠ 0 := by
    by_contra h
    apply h2
    apply Matrix.ext
    intro i j
    by_contra hz
    exact h ⟨i, j, hz⟩
  obtain ⟨i, j, hij⟩ := he
  let u : Fin 3 → F := fun k => if k = j then 1 else 0
  let v := N *ᵥ u
  let w := N *ᵥ v
  have hw : w i ≠ 0 := by
    rw [show w = (N * N) *ᵥ u from Matrix.mulVec_mulVec _ _ _]
    change (∑ k : Fin 3, (N * N) i k * (if k = j then 1 else 0)) ≠ 0
    rw [Finset.sum_eq_single j]
    · simpa using hij
    · intro k _ hk
      simp [hk]
    · simp
  have hNw : N *ᵥ w = 0 := by
    change N *ᵥ (N *ᵥ (N *ᵥ u)) = 0
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, h3,
      Matrix.zero_mulVec]
  let M : Mat F := fun k l => ![w k, v k, u k] l
  have hM (x : Fin 3 → F) :
      M *ᵥ x = x 0 • w + x 1 • v + x 2 • u := by
    funext k
    change (∑ l : Fin 3, M k l * x l) =
      x 0 * w k + x 1 * v k + x 2 * u k
    simp [M, Fin.sum_univ_three] <;> ring
  have hker (x : Fin 3 → F) (hx : M *ᵥ x = 0) : x = 0 := by
    rw [hM] at hx
    have h1 := congrArg (fun y : Fin 3 → F => N *ᵥ y) hx
    change N *ᵥ (x 0 • w + x 1 • v + x 2 • u) = N *ᵥ 0 at h1
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNw, smul_zero,
      zero_add, Matrix.mulVec_zero] at h1
    change x 1 • w + x 2 • v = 0 at h1
    have h2 := congrArg (fun y : Fin 3 → F => N *ᵥ y) h1
    change N *ᵥ (x 1 • w + x 2 • v) = N *ᵥ 0 at h2
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNw, smul_zero,
      zero_add, Matrix.mulVec_zero] at h2
    have h2i : x 2 * w i = 0 := congrFun h2 i
    have hx2 := (mul_eq_zero.mp h2i).resolve_right hw
    rw [hx2, zero_smul, add_zero] at h1
    have h1i : x 1 * w i = 0 := congrFun h1 i
    have hx1 := (mul_eq_zero.mp h1i).resolve_right hw
    simp only [hx2, hx1, zero_smul, add_zero] at hx
    have hxi : x 0 * w i = 0 := congrFun hx i
    have hx0 := (mul_eq_zero.mp hxi).resolve_right hw
    funext k
    fin_cases k <;> simp [hx0, hx1, hx2]
  have hinj : Function.Injective M.mulVec := by
    intro x y h
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, h, sub_self]
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  refine ⟨M, M⁻¹, hdet.ne_zero, Matrix.mul_nonsing_inv M hdet,
    Matrix.nonsing_inv_mul M hdet, ?_⟩
  apply Matrix.ext
  intro k l
  fin_cases l
  · have hz := congrFun hNw k
    simpa [M, rankTwo_jordanBlock, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.vecMul, Matrix.mulVec, dotProduct] using hz
  · simp [M, rankTwo_jordanBlock, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.vecMul, Matrix.mulVec, dotProduct, w]
  · simp [M, rankTwo_jordanBlock, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.vecMul, Matrix.mulVec, dotProduct, v]

end Frame

section Differential

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3

/-- Apply a derivation to every matrix entry. -/
def rankTwo_matrixDeriv (D : Derivation K (E K) (E K))
    (M : Matrix (Fin 3) (Fin 3) (E K)) : Matrix (Fin 3) (Fin 3) (E K) :=
  fun i j => D (M i j)

theorem rankTwo_matrixDeriv_mul (D : Derivation K (E K) (E K))
    (A C : Matrix (Fin 3) (Fin 3) (E K)) :
    rankTwo_matrixDeriv D (A * C) =
      A * rankTwo_matrixDeriv D C + rankTwo_matrixDeriv D A * C := by
  apply Matrix.ext
  intro i j
  simp only [rankTwo_matrixDeriv, Matrix.mul_apply, Matrix.add_apply,
    map_sum, Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- The differentiated cube-zero identity, in original coordinates. -/
theorem rankTwo_cubeDerivative
    (D : Derivation K (E K) (E K))
    (N : Matrix (Fin 3) (Fin 3) (E K)) (h3 : N ^ 3 = 0) :
    let P := rankTwo_matrixDeriv D N
    (N * N) * P + N * P * N + P * (N * N) = 0 := by
  let P := rankTwo_matrixDeriv D N
  have h : (N * N) * N = 0 := by
    simpa only [pow_succ, pow_zero, one_mul] using h3
  have hz := congrArg (rankTwo_matrixDeriv D) h
  rw [rankTwo_matrixDeriv_mul, rankTwo_matrixDeriv_mul] at hz
  have hzero : rankTwo_matrixDeriv D (0 : Matrix (Fin 3) (Fin 3) (E K)) = 0 := by
    apply Matrix.ext
    intro i j
    simp [rankTwo_matrixDeriv]
  rw [hzero, Matrix.add_mul, Matrix.mul_assoc P N N] at hz
  simpa only [add_assoc] using hz

/-- Differentiate the symmetric product HN without any frame
derivatives or inverse-gradient assumptions. -/
theorem rankTwo_selfAdjointDerivative
    (D : Derivation K (E K) (E K))
    (H N : Matrix (Fin 3) (Fin 3) (E K))
    (h : (H * N).transpose = H * N) :
    (rankTwo_matrixDeriv D H * N + H * rankTwo_matrixDeriv D N).transpose =
      rankTwo_matrixDeriv D H * N + H * rankTwo_matrixDeriv D N := by
  have he := congrArg (rankTwo_matrixDeriv D) h
  have ht : rankTwo_matrixDeriv D ((H * N).transpose) =
      (rankTwo_matrixDeriv D (H * N)).transpose := rfl
  rw [ht, rankTwo_matrixDeriv_mul, add_comm (H * rankTwo_matrixDeriv D N)] at he
  exact he

/-- The velocity derivative tensor is symmetric in its two input
slots, by commutation of the fraction-field partials. -/
theorem rankTwo_velocityTensor_symm
    (V : I → E K) (i j l : Fin 3) :
    rankTwo_matrixDeriv (rationalCharacteristicPartial l)
      (rationalCharacteristicJacobian V) i j =
    rankTwo_matrixDeriv (rationalCharacteristicPartial j)
      (rationalCharacteristicJacobian V) i l :=
  rationalCharacteristicPartial_comm l j (V (.inr i))

/-- The source Hessian derivative tensor has the same symmetry. -/
theorem rankTwo_hessianTensor_symm
    (f : B K) (i j l : Fin 3) :
    rankTwo_matrixDeriv (rationalCharacteristicPartial l)
      ((hessian f).map (algebraMap (B K) (E K))) i j =
    rankTwo_matrixDeriv (rationalCharacteristicPartial j)
      ((hessian f).map (algebraMap (B K) (E K))) i l := by
  simp only [rankTwo_matrixDeriv, Matrix.map_apply,
    rationalCharacteristicPartial_algebraMap, hessian_apply]
  rw [HC4.Newton.pderiv_comm_backport l j]

end Differential
end
end HC4.Polynomial.RankThreeCubic
