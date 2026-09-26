import HC4.Newton.RankOneThreeSchur
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelExactClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerFirstBreak
import Mathlib.Tactic

/-!
# Cleared 1+3 Schur clock for the zero-clock top-kernel seam

The maximal ordinary top face is a nonzero scalar multiple of one linear-form
power.  Its Hessian has rank one.  After moving the stored kernel coordinate
to slot 3, at least one of the first three diagonal Hessian entries is
nonzero.

The 2+2 Schur clock cannot start here because every constant 2x2 active minor
vanishes on a rank-one Hessian.  Instead we pivot on one nonzero scalar
diagonal and use the denominator-cleared 1+3 quotient from
`HC4.Newton.RankOneThreeSchur`.

For each possible scalar pivot:

* the quotient has zero constant 3x3 matrix, because every 2x2 Hessian minor
  of a linear power vanishes;
* its determinant is the square of the pivot series times the exact ordinary
  reverse-Rees clock `X^(4D-8)`;
* the pivot has nonzero constant coefficient.

Thus the remaining top-kernel seam is represented by an honest zero-special-
fibre 3x3 polynomial matrix with an exact determinant clock.  This is the
correct object for the subsequent rank-filtration / kernel-spending argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Every 2x2 Hessian minor of a scalar power of one linear form vanishes. -/
theorem hessianMinor_linearPower_eq_zero
    {nvar : ℕ}
    (a : K)
    (c : Fin nvar → K)
    (n : ℕ)
    (i j k l : Fin nvar) :
    HC4.Polynomial.hessian
          (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) i j *
        HC4.Polynomial.hessian
          (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) k l -
      HC4.Polynomial.hessian
          (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) i l *
        HC4.Polynomial.hessian
          (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) k j =
      0 := by
  repeat' rw [hessian_C_mul_gradientRatioLinearForm_pow_add_two_fin]
  simp only [MvPolynomial.C_mul]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The literal kernel-last parameter Hessian block used by the 1+3 clock. -/
noncomputable def threeSchurBlock
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate

/-- Constant coefficients of the kernel-last Hessian are exactly the Hessian
entries of the stored maximal top face in the same permuted coordinates. -/
theorem threeSchurBlock_coeff_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (i j : Fin 4) :
    (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate i j).coeff 0 =
      HC4.Polynomial.hessian T.topFace.face
        (kernelLastPerm kernelCoordinate i)
        (kernelLastPerm kernelCoordinate j) := by
  unfold kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  rw [parameterFirstHessian_coeff]
  rw [T.topKernelReverseRees_layer_zero_eq_topFace]

/-- Hence every constant 2x2 minor of the kernel-last block vanishes. -/
theorem threeSchurBlock_constantMinor_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (i j k l : Fin 4) :
    (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate i j).coeff 0 *
        (kernelLastParameterFirstHessian
          T.topKernelReverseReesFamily kernelCoordinate k l).coeff 0 -
      (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate i l).coeff 0 *
        (kernelLastParameterFirstHessian
          T.topKernelReverseReesFamily kernelCoordinate k j).coeff 0 = 0 := by
  repeat' rw [P.threeSchurBlock_coeff_zero]
  obtain ⟨n, hD⟩ : ∃ n : ℕ, T.topFace.degree = n + 2 := by
    have hge : 3 ≤ T.topFace.degree := T.topFace_degree_ge_three
    refine ⟨T.topFace.degree - 2, ?_⟩
    omega
  rw [P.eq_power, hD]
  exact hessianMinor_linearPower_eq_zero
    P.coefficient P.ratio n
    (kernelLastPerm kernelCoordinate i)
    (kernelLastPerm kernelCoordinate j)
    (kernelLastPerm kernelCoordinate k)
    (kernelLastPerm kernelCoordinate l)

/-- The kernel-last block retains the exact ordinary reverse-Rees determinant
clock. -/
theorem threeSchurBlock_determinantCore
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.threeSchurBlock.determinantCore =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
        T.topKernelOrdinaryReesDefect := by
  unfold threeSchurBlock
  exact kernelLastFamilyHessianFourBlock_determinantCore_eq_X_pow
    T.topKernelReverseReesFamily kernelCoordinate
    T.topKernelReverseReesFamily_hasHessianDefect

/-- Source-facing zero-special-fibre 1+3 Schur packet. -/
inductive TopKernelThreeSchurClockData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)

  | pivotA
      (pivot_ne_zero : P.threeSchurBlock.a.coeff 0 ≠ 0)
      (constant_zero :
        ∀ i j : Fin 3,
          (P.threeSchurBlock.rankOneClearedThreeSchurMatrix i j).coeff 0 = 0)
      (determinant_clock :
        P.threeSchurBlock.rankOneClearedThreeSchurMatrix.det =
          P.threeSchurBlock.a ^ 2 *
            (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
              T.topKernelOrdinaryReesDefect)

  | pivotD
      (pivot_ne_zero : P.threeSchurBlock.d.coeff 0 ≠ 0)
      (constant_zero :
        ∀ i j : Fin 3,
          (P.threeSchurBlock.rankOneClearedThreeSchurMatrixD i j).coeff 0 = 0)
      (determinant_clock :
        P.threeSchurBlock.rankOneClearedThreeSchurMatrixD.det =
          P.threeSchurBlock.d ^ 2 *
            (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
              T.topKernelOrdinaryReesDefect)

  | pivotX
      (pivot_ne_zero : P.threeSchurBlock.x.coeff 0 ≠ 0)
      (constant_zero :
        ∀ i j : Fin 3,
          (P.threeSchurBlock.rankOneClearedThreeSchurMatrixX i j).coeff 0 = 0)
      (determinant_clock :
        P.threeSchurBlock.rankOneClearedThreeSchurMatrixX.det =
          P.threeSchurBlock.x ^ 2 *
            (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
              T.topKernelOrdinaryReesDefect)

private theorem threeSchurBlock_coeff_zero_symm
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (i j : Fin 4) :
    (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate i j).coeff 0 =
      (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate j i).coeff 0 := by
  unfold kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact congrArg
    (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0)
    (parameterFirstHessian_symmetric
      T.topKernelReverseReesFamily
      (kernelLastPerm kernelCoordinate i)
      (kernelLastPerm kernelCoordinate j))

private theorem threeSchurBlock_constantPivotMinor_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (p u v : Fin 4) :
    (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate p p).coeff 0 *
        (kernelLastParameterFirstHessian
          T.topKernelReverseReesFamily kernelCoordinate u v).coeff 0 -
      (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate p u).coeff 0 *
        (kernelLastParameterFirstHessian
          T.topKernelReverseReesFamily kernelCoordinate p v).coeff 0 = 0 := by
  have hm := P.threeSchurBlock_constantMinor_zero p p u v
  have hs := P.threeSchurBlock_coeff_zero_symm u p
  rw [hs] at hm
  simpa [mul_comm] using hm

set_option maxHeartbeats 2000000 in
private theorem rankOneClearedThreeSchurMatrix_coeff_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    ∀ i j : Fin 3,
      (P.threeSchurBlock.rankOneClearedThreeSchurMatrix i j).coeff 0 = 0 := by
  let B := P.threeSchurBlock
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [GeneralFourBlock.rankOneClearedThreeSchurMatrix,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Polynomial.coeff_sub, Polynomial.coeff_mul] <;>
    change _ = 0
  all_goals
    first
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (0 : Fin 4) 1 1
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (0 : Fin 4) 1 2
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (0 : Fin 4) 1 3
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (0 : Fin 4) 2 2
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (0 : Fin 4) 2 3
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (0 : Fin 4) 3 3

set_option maxHeartbeats 2000000 in
private theorem rankOneClearedThreeSchurMatrixD_coeff_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    ∀ i j : Fin 3,
      (P.threeSchurBlock.rankOneClearedThreeSchurMatrixD i j).coeff 0 = 0 := by
  let B := P.threeSchurBlock
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [GeneralFourBlock.rankOneClearedThreeSchurMatrixD,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Polynomial.coeff_sub, Polynomial.coeff_mul] <;>
    change _ = 0
  all_goals
    first
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (1 : Fin 4) 0] using
        P.threeSchurBlock_constantPivotMinor_zero (1 : Fin 4) 0 0
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (1 : Fin 4) 0] using
        P.threeSchurBlock_constantPivotMinor_zero (1 : Fin 4) 0 2
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (1 : Fin 4) 0] using
        P.threeSchurBlock_constantPivotMinor_zero (1 : Fin 4) 0 3
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (1 : Fin 4) 2 2
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (1 : Fin 4) 2 3
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (1 : Fin 4) 3 3

set_option maxHeartbeats 2000000 in
private theorem rankOneClearedThreeSchurMatrixX_coeff_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    ∀ i j : Fin 3,
      (P.threeSchurBlock.rankOneClearedThreeSchurMatrixX i j).coeff 0 = 0 := by
  let B := P.threeSchurBlock
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [GeneralFourBlock.rankOneClearedThreeSchurMatrixX,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Polynomial.coeff_sub, Polynomial.coeff_mul] <;>
    change _ = 0
  all_goals
    first
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 0,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 1] using
        P.threeSchurBlock_constantPivotMinor_zero (2 : Fin 4) 0 0
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 0,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 1] using
        P.threeSchurBlock_constantPivotMinor_zero (2 : Fin 4) 0 1
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 0,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 1] using
        P.threeSchurBlock_constantPivotMinor_zero (2 : Fin 4) 0 3
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 0,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 1] using
        P.threeSchurBlock_constantPivotMinor_zero (2 : Fin 4) 1 1
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 0,
        P.threeSchurBlock_coeff_zero_symm (2 : Fin 4) 1] using
        P.threeSchurBlock_constantPivotMinor_zero (2 : Fin 4) 1 3
    | simpa [B, threeSchurBlock, kernelLastFamilyHessianFourBlock,
        GeneralFourBlock.ofSymmetricMatrix] using
        P.threeSchurBlock_constantPivotMinor_zero (2 : Fin 4) 3 3

/- The scalar-pivot rank-one top face always produces the exact 1+3 Schur
clock packet. -/
theorem threeSchurClockData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelThreeSchurClockData := by
  let B := P.threeSchurBlock
  have hactive :
      B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 := by
    simpa [B, threeSchurBlock] using
      P.kernelLastBlock_activeDiagonal_coeff_zero_ne_zero
  rcases hactive with ha | hd | hx
  · exact ⟨.pivotA ha P.rankOneClearedThreeSchurMatrix_coeff_zero (by
      rw [B.det_rankOneClearedThreeSchurMatrix]
      rw [P.threeSchurBlock_determinantCore])⟩
  · exact ⟨.pivotD hd P.rankOneClearedThreeSchurMatrixD_coeff_zero (by
      rw [B.det_rankOneClearedThreeSchurMatrixD]
      rw [P.threeSchurBlock_determinantCore])⟩
  · exact ⟨.pivotX hx P.rankOneClearedThreeSchurMatrixX_coeff_zero (by
      rw [B.det_rankOneClearedThreeSchurMatrixX]
      rw [P.threeSchurBlock_determinantCore])⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
