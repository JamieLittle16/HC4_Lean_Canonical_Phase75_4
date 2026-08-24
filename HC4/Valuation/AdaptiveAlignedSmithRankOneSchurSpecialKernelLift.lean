import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianSpecialFiber
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurTangentialRawRay
import HC4.Newton.GeneralFourBlockKernelLift
import Mathlib.Tactic

/-!
# Denominator-cleared full special-fibre kernel behind rank-one Schur closing

The retained rank-one Schur chart is source-honest up to the point where its
binary Schur block is aligned.  To avoid treating that polynomial-valued
alignment as a source coordinate change, we work with the raw constant Schur
block and lift its kernel directly to the full special-fibre Hessian block.

For either retained pivot, this produces nonzero binary data `(u,v)` and the
polynomial vector

    (-adj(A) B (u,v), det(A) (u,v))

in the kernel of the actual finite four-block in the same honest chart.
The active determinant is nonzero, so the lifted vector is nonzero.

This is the exact object on which the remaining Smith/RS2 polynomialisation
argument must act: the next theorem only has to show that its projective
source direction is constant (or expose certified repair).
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The finite special-fibre four-block in the exact honest chart retained by
the closing carrier. -/
noncomputable def specialFourBlock
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  parameterConstantCoeffFourBlock C.chartData.schurData.block

/-- Binary raw-Schur kernel data retained before any polynomial-valued
alignment. -/
structure DenominatorClearedSpecialSchurKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  u : MvPolynomial (Fin 4) K
  v : MvPolynomial (Fin 4) K
  binary_ne_zero : u ≠ 0 ∨ v ≠ 0
  schurKernel : C.specialFourBlock.IsClearedSchurKernel u v

namespace DenominatorClearedSpecialSchurKernelData

/-- Full polynomial kernel vector in the honest four-block chart. -/
noncomputable def fullVector
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DenominatorClearedSpecialSchurKernelData C) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  C.specialFourBlock.clearedKernelLift D.u D.v

/-- The denominator-cleared lift is genuinely in the kernel of the full
special-fibre block. -/
theorem fullVector_kernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DenominatorClearedSpecialSchurKernelData C) :
    C.specialFourBlock.matrix.mulVec D.fullVector = 0 := by
  exact
    C.specialFourBlock.mulVec_clearedKernelLift_eq_zero
      D.u D.v D.schurKernel

/-- The full lifted vector is nonzero because the special active determinant
is nonzero and at least one binary kernel coordinate is nonzero. -/
theorem fullVector_ne_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DenominatorClearedSpecialSchurKernelData C) :
    D.fullVector ≠ 0 := by
  have hactive : C.specialFourBlock.activeDet ≠ 0 := by
    change
      (parameterConstantCoeffFourBlock C.chartData.schurData.block).activeDet ≠ 0
    rw [← parameterConstantCoeffFourBlock_activeDet]
    exact C.chartData.schurData.activeDet_coeff_zero_ne_zero
  rcases D.binary_ne_zero with hu | hv
  · intro hzero
    have hcoord := congrFun hzero (2 : Fin 4)
    simp [fullVector, GeneralFourBlock.clearedKernelLift] at hcoord
    rcases hcoord with hactive0 | hu0
    · exact hactive hactive0
    · exact hu hu0
  · intro hzero
    have hcoord := congrFun hzero (3 : Fin 4)
    simp [fullVector, GeneralFourBlock.clearedKernelLift] at hcoord
    rcases hcoord with hactive0 | hv0
    · exact hactive hactive0
    · exact hv hv0

end DenominatorClearedSpecialSchurKernelData

/-- Every retained rank-one Schur pivot canonically supplies a nonzero raw
binary kernel, hence a nonzero denominator-cleared full polynomial kernel in
the honest special-fibre chart. -/
theorem exists_denominatorClearedSpecialSchurKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    Nonempty (DenominatorClearedSpecialSchurKernelData C) := by
  let H := C.chartData.schurData.block
  let H0 := C.specialFourBlock
  let S := H.polynomialSchurSeries
  generalize hp : C.chartData.schurData.chosenPivot = p
  cases p with
  | left hleft =>
      let u : MvPolynomial (Fin 4) K := -(S.offDiag.coeff 0)
      let v : MvPolynomial (Fin 4) K := S.active.coeff 0
      have huv : u ≠ 0 ∨ v ≠ 0 := by
        exact Or.inr hleft.1
      have hA : H0.schurA = S.active.coeff 0 := by
        simpa [H0, S, GeneralFourBlock.polynomialSchurSeries] using
          (parameterConstantCoeffFourBlock_schurA H).symm
      have hB : H0.schurB = S.offDiag.coeff 0 := by
        simpa [H0, S, GeneralFourBlock.polynomialSchurSeries] using
          (parameterConstantCoeffFourBlock_schurB H).symm
      have hC : H0.schurC = S.kernel.coeff 0 := by
        simpa [H0, S, GeneralFourBlock.polynomialSchurSeries] using
          (parameterConstantCoeffFourBlock_schurC H).symm
      have hker : H0.IsClearedSchurKernel u v := by
        unfold GeneralFourBlock.IsClearedSchurKernel
        constructor
        · dsimp [u, v]
          rw [hA, hB]
          ring
        · dsimp [u, v]
          rw [hB, hC]
          rw [mul_comm (S.kernel.coeff 0) (S.active.coeff 0), hleft.2]
          ring
      exact ⟨{
        u := u
        v := v
        binary_ne_zero := huv
        schurKernel := hker
      }⟩
  | right hright =>
      let u : MvPolynomial (Fin 4) K := 1
      let v : MvPolynomial (Fin 4) K := 0
      have huv : u ≠ 0 ∨ v ≠ 0 := by
        left
        simp [u]
      have hA : H0.schurA = S.active.coeff 0 := by
        simpa [H0, S, GeneralFourBlock.polynomialSchurSeries] using
          (parameterConstantCoeffFourBlock_schurA H).symm
      have hB : H0.schurB = S.offDiag.coeff 0 := by
        simpa [H0, S, GeneralFourBlock.polynomialSchurSeries] using
          (parameterConstantCoeffFourBlock_schurB H).symm
      have hker : H0.IsClearedSchurKernel u v := by
        unfold GeneralFourBlock.IsClearedSchurKernel
        constructor
        · dsimp [u, v]
          simp only [mul_one, mul_zero, add_zero]
          rw [hA]
          exact hright.1
        · dsimp [u, v]
          simp only [mul_one, mul_zero, add_zero]
          rw [hB]
          exact hright.2.1
      exact ⟨{
        u := u
        v := v
        binary_ne_zero := huv
        schurKernel := hker
      }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
