import HC4.Polynomial.RationalCharacteristicRankTwoDualLine

/-!
# Rank-two Frobenius tensor calculation

The pointwise calculation underlying involutivity of the image plane.
Unlike a normalization to the antidiagonal identity, the Jordan frame
below retains the general symmetric invertible Hessian and requires no
square roots or algebraic closure.

The two inputs are the differentiated cube-zero equation and the
differentiated Hessian self-adjointness equation. The velocity second
derivative tensor is symmetric in the two input slots and the Hessian
third derivative tensor is symmetric in its input slots.

This file isolates the finite-dimensional tensor calculation. Its
transport to the original rational differential system is separate.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

variable {F : Type*} [Field F]

/-- The rank-two Jordan block over the actual coefficient field. -/
def rankTwo_jordanBlock : Matrix (Fin 3) (Fin 3) F :=
  !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- Every symmetric symmetrizer of the regular nilpotent Jordan block
has this form, without a further normalization. -/
theorem rankTwo_jordan_hessian_form
    (H : Matrix (Fin 3) (Fin 3) F)
    (hs : H.transpose = H)
    (hself : rankTwo_jordanBlock.transpose * H = H * rankTwo_jordanBlock) :
    H = !![0, 0, H 0 2; 0, H 0 2, H 1 2; H 0 2, H 1 2, H 2 2] := by
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) hself
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) hself
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 2) hself
  have hs01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) hs
  have hs02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) hs
  have hs12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 2) hs
  simp [rankTwo_jordanBlock, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.transpose_apply] at h01 h02 h12 hs01 hs02 hs12
  have hz00 : H 0 0 = 0 := by simpa using h01.symm
  have hz01 : H 0 1 = 0 := by simpa using h02.symm
  have he11 : H 1 1 = H 0 2 := h12.symm
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hz00, hz01, he11, hs01, hs02, hs12]

/-- Differentiate J³=0. Its three entries in the first row give
the three linear constraints on the derivative matrix. -/
theorem rankTwo_jordan_cubeDerivative_constraints
    (P : Matrix (Fin 3) (Fin 3) F)
    (h : (rankTwo_jordanBlock * rankTwo_jordanBlock) * P +
      rankTwo_jordanBlock * P * rankTwo_jordanBlock +
      P * (rankTwo_jordanBlock * rankTwo_jordanBlock) = 0) :
    P 2 0 = 0 ∧ P 2 1 + P 1 0 = 0 ∧
      P 2 2 + P 1 1 + P 0 0 = 0 := by
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) h
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) h
  have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) h
  simp [rankTwo_jordanBlock, Matrix.add_apply, Matrix.mul_apply,
    Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

variable [CharZero F]

/-- Finite tensor form of the rank-two Frobenius identity. The
out-of-plane second derivative in the middle Jordan direction
must vanish. No differential geometry or classification theorem
is used in this calculation. -/
theorem rankTwo_jordan_frobenius_tensor
    (a b c : F) (ha : a ≠ 0)
    (P T : Fin 3 → Matrix (Fin 3) (Fin 3) F)
    (hP : ∀ i j l : Fin 3, P l i j = P j i l)
    (hT : ∀ i j l : Fin 3, T l i j = T j i l)
    (h3 : ∀ l : Fin 3,
      (rankTwo_jordanBlock * rankTwo_jordanBlock) * P l +
      rankTwo_jordanBlock * P l * rankTwo_jordanBlock +
      P l * (rankTwo_jordanBlock * rankTwo_jordanBlock) = 0)
    (hself : ∀ l : Fin 3,
      let H : Matrix (Fin 3) (Fin 3) F := !![0, 0, a; 0, a, b; a, b, c]
      (T l * rankTwo_jordanBlock + H * P l).transpose =
        T l * rankTwo_jordanBlock + H * P l) :
    P 1 2 1 = 0 := by
  have hc0 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (P l) (h3 l)).1
  have hc1 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (P l) (h3 l)).2.1
  have hc2 (l : Fin 3) := (rankTwo_jordan_cubeDerivative_constraints (P l) (h3 l)).2.2
  have hs01 (l : Fin 3) :
      T l 0 0 + a * P l 2 1 = a * P l 1 0 + b * P l 2 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 0) (hself l)
    simpa [rankTwo_jordanBlock, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.vecMul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] using h
  have hs02 (l : Fin 3) :
      T l 0 1 + a * P l 2 2 =
        a * P l 0 0 + b * P l 1 0 + c * P l 2 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 0) (hself l)
    simpa [rankTwo_jordanBlock, Matrix.add_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.vecMul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] using h
  have hz1 : P 0 2 1 = 0 := (hP 2 1 0).trans (hc0 1)
  have hz2 : P 0 2 2 = 0 := (hP 2 2 0).trans (hc0 2)
  have hz3 : P 0 1 0 = 0 := by
    have h := hc1 0
    rw [hz1, zero_add] at h
    exact h
  have hp : P 0 1 1 = -P 1 2 1 := by
    rw [hP 1 1 0]
    have h := hc1 1
    linear_combination h
  have hdiag : P 0 0 0 = P 1 2 1 := by
    have h := hc2 0
    rw [hz2, hp] at h
    linear_combination h
  have hA := hs01 1
  have hB := hs02 0
  rw [hc0 1, mul_zero, add_zero] at hA
  simp only [hz2, hz3, hc0 0, mul_zero, add_zero, hdiag] at hB
  have ht : T 1 0 0 = T 0 0 1 := hT 0 0 1
  have hz : (3 : F) * a * P 1 2 1 = 0 := by
    linear_combination hA - hB - ht + a * hc1 1
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) ha)

end
end HC4.Polynomial.RankThreeCubic
