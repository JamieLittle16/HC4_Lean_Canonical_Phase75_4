import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelFirstBreakMixedNonlinear
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurPrincipalFrontier
import Mathlib.Tactic

/-!
# Tangent versus transverse opening of the top-kernel three-Schur quotient

The source-honest first kernel-row break occurs at a physical reverse-Rees
order j.  In the surviving mixed branch its exact source layer has

    H_kk^(j) = 0,    H_ik^(j) != 0

for the stored top-face kernel coordinate k.

After pivoting off one nonzero scalar direction of the rank-one top Hessian,
the cleared 1+3 Schur quotient has kernel slot 2 in every pivot orientation.
At the same physical order j its kernel diagonal is still zero.  Therefore
there are exactly two possibilities:

* one quotient mixed entry at (0,2) or (1,2) is nonzero; then the exact
  coefficient matrix at order j already has a nonzero coordinate-principal
  2x2 minor;
* both quotient mixed entries vanish; then the whole quotient kernel column
  vanishes at order j even though the original Hessian kernel row opened.
  This is the precise source-honest tangent-to-rank-one-cone alternative.

No claim that the tangent branch is contradictory is made here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Exact coefficient matrix of the cleared 1+3 quotient at the physical
first kernel-row order retained by the mixed source layer. -/
noncomputable def threeSchurCoefficientMatrixAtFirstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 4) K) :=
  fun i j =>
    (S.toExactZeroThreeSchurClock.zeroSeries.matrix i j).coeff
      M.mixed.layer.order

private theorem firstBreak_kernelRow_lower_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    ∀ n : ℕ, n < M.mixed.layer.order →
      B.q.coeff n = 0 ∧ B.s.coeff n = 0 ∧
        B.y.coeff n = 0 ∧ B.z.coeff n = 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
  intro n hn
  have horder := M.mixed.layer.order_is_firstBreak
  have hn' :
      n <
        firstFourBlockKernelRowBreakOrder B hrow := by
    simpa [B, hrow] using (show n < M.mixed.layer.order from hn)
  exact firstFourBlockKernelRowBreakOrder_lower_zero B hrow hn'

private theorem firstBreak_rawKernelDiagonal_eq_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.z.coeff M.mixed.layer.order = 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  have hz :
      (parameterFirstHessian T.topKernelReverseReesFamily
        kernelCoordinate kernelCoordinate).coeff
          M.mixed.layer.order = 0 := by
    rw [parameterFirstHessian_coeff, M.mixed.layer.exactLayer]
    exact M.mixed.kernelDiagonal_eq_zero
  simpa [B, kernelLastFamilyHessianFourBlock,
    GeneralFourBlock.ofSymmetricMatrix,
    kernelLastParameterFirstHessian] using hz

/-- The cleared 1+3 quotient kernel diagonal is zero at the physical first
kernel-row opening order, in every scalar-pivot orientation. -/
theorem threeSchurCoefficientMatrixAtFirstBreak_kernelDiagonal_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    M.threeSchurCoefficientMatrixAtFirstBreak S 2 2 = 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let j := M.mixed.layer.order
  have hj : 0 < j := by
    simpa [j] using M.mixed.layer.order_pos
  have hlower := M.firstBreak_kernelRow_lower_zero
  have hqLower : ∀ n : ℕ, n < j → B.q.coeff n = 0 :=
    fun n hn => (hlower n (by simpa [j] using hn)).1
  have hsLower : ∀ n : ℕ, n < j → B.s.coeff n = 0 :=
    fun n hn => (hlower n (by simpa [j] using hn)).2.1
  have hyLower : ∀ n : ℕ, n < j → B.y.coeff n = 0 :=
    fun n hn => (hlower n (by simpa [j] using hn)).2.2.1
  have hzLower : ∀ n : ℕ, n < j → B.z.coeff n = 0 :=
    fun n hn => (hlower n (by simpa [j] using hn)).2.2.2
  have hzj : B.z.coeff j = 0 := by
    simpa [B, j] using M.firstBreak_rawKernelDiagonal_eq_zero
  cases S with
  | pivotA hpivot hzero hdet =>
      change
        (B.a * B.z - B.q * B.q).coeff j = 0
      have haz :
          (B.a * B.z).coeff j = B.a.coeff 0 * B.z.coeff j :=
        coeff_mul_eq_constant_mul_of_right_vanishes_below
          B.a B.z hzLower
      have hqq :
          (B.q * B.q).coeff j = 0 :=
        coeff_kernelPair_eq_zero_through
          B.q B.q hj hqLower hqLower j le_rfl
      rw [Polynomial.coeff_sub, haz, hqq, hzj]
      simp
  | pivotD hpivot hzero hdet =>
      change
        (B.d * B.z - B.s * B.s).coeff j = 0
      have hdz :
          (B.d * B.z).coeff j = B.d.coeff 0 * B.z.coeff j :=
        coeff_mul_eq_constant_mul_of_right_vanishes_below
          B.d B.z hzLower
      have hss :
          (B.s * B.s).coeff j = 0 :=
        coeff_kernelPair_eq_zero_through
          B.s B.s hj hsLower hsLower j le_rfl
      rw [Polynomial.coeff_sub, hdz, hss, hzj]
      simp
  | pivotX hpivot hzero hdet =>
      change
        (B.x * B.z - B.y * B.y).coeff j = 0
      have hxz :
          (B.x * B.z).coeff j = B.x.coeff 0 * B.z.coeff j :=
        coeff_mul_eq_constant_mul_of_right_vanishes_below
          B.x B.z hzLower
      have hyy :
          (B.y * B.y).coeff j = 0 :=
        coeff_kernelPair_eq_zero_through
          B.y B.y hj hyLower hyLower j le_rfl
      rw [Polynomial.coeff_sub, hxz, hyy, hzj]
      simp

/-- The exact physical first-break quotient matrix is symmetric. -/
theorem threeSchurCoefficientMatrixAtFirstBreak_isSymm
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    (M.threeSchurCoefficientMatrixAtFirstBreak S).IsSymm := by
  intro i j
  have hs := S.exactZeroThreeSchurClock_isSymm i j
  exact congrArg
    (fun p : Polynomial (MvPolynomial (Fin 4) K) =>
      p.coeff M.mixed.layer.order) hs

/-- A genuinely projected mixed opening gives a principal rank-two
coefficient block at the exact first source layer. -/
structure ThreeSchurProjectedRankTwoAtFirstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Prop where
  index : Fin 2
  mixed_ne_zero :
    M.threeSchurCoefficientMatrixAtFirstBreak S index.castSucc 2 ≠ 0
  principalMinor_ne_zero :
    M.threeSchurCoefficientMatrixAtFirstBreak S index.castSucc index.castSucc *
          M.threeSchurCoefficientMatrixAtFirstBreak S 2 2 -
        M.threeSchurCoefficientMatrixAtFirstBreak S index.castSucc 2 *
          M.threeSchurCoefficientMatrixAtFirstBreak S 2 index.castSucc ≠ 0

/-- The complementary case: the first actual Hessian kernel-row opening is
invisible in the 1+3 quotient, so the quotient kernel column remains zero at
that same physical order. -/
structure ThreeSchurTangentAtFirstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Prop where
  mixed0_zero :
    M.threeSchurCoefficientMatrixAtFirstBreak S 0 2 = 0
  mixed1_zero :
    M.threeSchurCoefficientMatrixAtFirstBreak S 1 2 = 0
  diagonal_zero :
    M.threeSchurCoefficientMatrixAtFirstBreak S 2 2 = 0

/-- **Source-honest tangent split at the first kernel-row opening.** -/
theorem projectedRankTwo_or_tangentAtFirstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    S.ThreeSchurProjectedRankTwoAtFirstBreak M ∨
      S.ThreeSchurTangentAtFirstBreak M := by
  have hdiag :=
    M.threeSchurCoefficientMatrixAtFirstBreak_kernelDiagonal_zero S
  have hsymm :=
    M.threeSchurCoefficientMatrixAtFirstBreak_isSymm S
  by_cases h0 :
      M.threeSchurCoefficientMatrixAtFirstBreak S 0 2 = 0
  · by_cases h1 :
        M.threeSchurCoefficientMatrixAtFirstBreak S 1 2 = 0
    · exact Or.inr ⟨h0, h1, hdiag⟩
    · left
      refine ⟨0, h1, ?_⟩
      have hs :
          M.threeSchurCoefficientMatrixAtFirstBreak S 2 0 =
            M.threeSchurCoefficientMatrixAtFirstBreak S 0 2 :=
        hsymm 2 0
      rw [hdiag, hs]
      simp only [mul_zero, zero_mul, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero h1 h1)
  · left
    refine ⟨0, h0, ?_⟩
    have hs :
        M.threeSchurCoefficientMatrixAtFirstBreak S 2 0 =
          M.threeSchurCoefficientMatrixAtFirstBreak S 0 2 :=
      hsymm 2 0
    rw [hdiag, hs]
    simp only [mul_zero, zero_mul, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero h0 h0)

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
