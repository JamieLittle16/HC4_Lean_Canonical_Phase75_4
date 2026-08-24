import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyDirectionalRemainder
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurSpecialKernelLift
import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianShearCharts
import Mathlib.Tactic

/-!
# Removing the auxiliary swap/shear from the early-Schur special kernel

The Stage-4B first source key lives in the honest right-recentered source
coordinates (up to the retained coordinate permutation `rho`).  The
Stage-3 denominator-cleared Schur kernel, however, is initially expressed in
one of the three determinant-preserving Hessian charts used by the closing
frontier:

* the coordinate chart;
* the `0 <-> 2` swap chart;
* the elementary `e₀ <- e₀ + e₂` shear chart.

Before comparing that kernel with an initial form of the source polynomial we
must remove the auxiliary swap/shear.  This file does exactly that, and
nothing more.

The vector transforms are the literal basis transforms represented by the
already-green `GeneralFourBlock.swap02` and `GeneralFourBlock.shear02`.
Consequently every denominator-cleared special Schur kernel gives a nonzero
polynomial kernel of the *coordinate-permuted honest special-fibre Hessian*.

After this theorem the only remaining coordinate discrepancy between the
Stage-4B source key and the Schur kernel is the retained permutation `rho`.
That permutation is source-honest and is handled by the existing coordinate-
permutation/Hessian covariance machinery; no new shear geometry is needed.
-/

namespace HC4.Newton

noncomputable section

universe v

variable {R : Type v} [CommRing R]

/-- Vector transform for the simultaneous `0 <-> 2` basis swap. -/
def swap02KernelVector (w : Fin 4 → R) : Fin 4 → R :=
  ![w 2, w 1, w 0, w 3]

/-- Vector transform from the sheared coordinates back to the unsheared
coordinates for `e₀ ↦ e₀ + e₂`. -/
def shear02KernelVector (w : Fin 4 → R) : Fin 4 → R :=
  ![w 0, w 1, w 0 + w 2, w 3]

/-- Covector transform occurring on the output side of the same shear. -/
def shear02OutputVector (w : Fin 4 → R) : Fin 4 → R :=
  ![w 0 + w 2, w 1, w 2, w 3]

@[simp] theorem swap02KernelVector_zero :
    swap02KernelVector (R := R) (0 : Fin 4 → R) = 0 := by
  funext i
  fin_cases i <;> simp [swap02KernelVector]

@[simp] theorem shear02KernelVector_zero :
    shear02KernelVector (R := R) (0 : Fin 4 → R) = 0 := by
  funext i
  fin_cases i <;> simp [shear02KernelVector]

@[simp] theorem shear02OutputVector_zero :
    shear02OutputVector (R := R) (0 : Fin 4 → R) = 0 := by
  funext i
  fin_cases i <;> simp [shear02OutputVector]

/-- Swapping twice is the identity. -/
theorem swap02KernelVector_involutive (w : Fin 4 → R) :
    swap02KernelVector (swap02KernelVector w) = w := by
  funext i
  fin_cases i <;> simp [swap02KernelVector]

/-- The swap vector transform is injective. -/
theorem swap02KernelVector_injective :
    Function.Injective (swap02KernelVector (R := R)) := by
  intro u w h
  have h' := congrArg (swap02KernelVector (R := R)) h
  simpa [swap02KernelVector_involutive] using h'

/-- The input shear vector transform is injective. -/
theorem shear02KernelVector_injective :
    Function.Injective (shear02KernelVector (R := R)) := by
  intro u w h
  funext i
  fin_cases i
  · simpa [shear02KernelVector] using congrFun h (0 : Fin 4)
  · simpa [shear02KernelVector] using congrFun h (1 : Fin 4)
  · have h0 : u (0 : Fin 4) = w 0 := by
      simpa [shear02KernelVector] using congrFun h (0 : Fin 4)
    have h2 : u 0 + u 2 = w 0 + w 2 := by
      simpa [shear02KernelVector] using congrFun h (2 : Fin 4)
    rw [h0] at h2
    simpa using (add_left_cancel h2)
  · simpa [shear02KernelVector] using congrFun h (3 : Fin 4)

/-- The output shear transform is injective. -/
theorem shear02OutputVector_injective :
    Function.Injective (shear02OutputVector (R := R)) := by
  intro u w h
  funext i
  fin_cases i
  · have h0 : u 0 + u 2 = w 0 + w 2 := by
      simpa [shear02OutputVector] using congrFun h (0 : Fin 4)
    have h2 : u (2 : Fin 4) = w 2 := by
      simpa [shear02OutputVector] using congrFun h (2 : Fin 4)
    rw [h2] at h0
    simpa using (add_right_cancel h0)
  · simpa [shear02OutputVector] using congrFun h (1 : Fin 4)
  · simpa [shear02OutputVector] using congrFun h (2 : Fin 4)
  · simpa [shear02OutputVector] using congrFun h (3 : Fin 4)

namespace GeneralFourBlock

/-- Exact matrix/vector covariance of the `0 <-> 2` block swap. -/
theorem swap02_matrix_mulVec
    (H : GeneralFourBlock R)
    (w : Fin 4 → R) :
    H.swap02.matrix.mulVec w =
      swap02KernelVector (H.matrix.mulVec (swap02KernelVector w)) := by
  funext i
  fin_cases i <;>
    simp [matrix, swap02, swap02KernelVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four] <;>
    ring

/-- A kernel in the swapped chart transports back to a kernel of the original
four-block. -/
theorem mulVec_swap02KernelVector_eq_zero
    (H : GeneralFourBlock R)
    (w : Fin 4 → R)
    (hker : H.swap02.matrix.mulVec w = 0) :
    H.matrix.mulVec (swap02KernelVector w) = 0 := by
  apply swap02KernelVector_injective (R := R)
  rw [← H.swap02_matrix_mulVec w, hker]
  simp

/-- Exact matrix/vector covariance of the elementary `0 <- 0 + 2` shear. -/
theorem shear02_matrix_mulVec
    (H : GeneralFourBlock R)
    (w : Fin 4 → R) :
    H.shear02.matrix.mulVec w =
      shear02OutputVector
        (H.matrix.mulVec (shear02KernelVector w)) := by
  funext i
  fin_cases i <;>
    simp [matrix, shear02, shear02KernelVector, shear02OutputVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    ring

/-- A kernel in the sheared chart transports back to a kernel of the original
four-block. -/
theorem mulVec_shear02KernelVector_eq_zero
    (H : GeneralFourBlock R)
    (w : Fin 4 → R)
    (hker : H.shear02.matrix.mulVec w = 0) :
    H.matrix.mulVec (shear02KernelVector w) = 0 := by
  apply shear02OutputVector_injective (R := R)
  rw [← H.shear02_matrix_mulVec w, hker]
  simp

end GeneralFourBlock

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Parameter-zero specialisation commutes with the `0 <-> 2` block swap.
The analogous shear theorem already exists in
`AdaptiveAlignedSmithRecenteredHessianShearCharts`. -/
theorem parameterConstantCoeffFourBlock_swap02
    (H : GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K))) :
    parameterConstantCoeffFourBlock H.swap02 =
      (parameterConstantCoeffFourBlock H).swap02 := by
  ext <;>
    simp [parameterConstantCoeffFourBlock, GeneralFourBlock.swap02]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The finite honest special-fibre Hessian block before the auxiliary
swap/shear, but still in the retained coordinate permutation `rho`. -/
noncomputable def coordinateSpecialFourBlock
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
    C.chartData.chart.rho B.aligned.endpoint

/-- In a coordinate chart the Stage-3 special four-block is literally the
coordinate-permuted honest special Hessian. -/
theorem specialFourBlock_eq_coordinateSpecialFourBlock_of_coordinate
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hkind : C.chartData.chart.kind =
      AdaptiveAlignedRightRecenteredHessianChartKind.coordinate) :
    C.specialFourBlock = C.coordinateSpecialFourBlock := by
  unfold specialFourBlock coordinateSpecialFourBlock
  rw [C.schurBlock_eq_chartBlock]
  unfold AdaptiveAlignedRightRecenteredExactHessianChart.block
  rw [hkind]
  simp only [adaptiveAlignedRightRecenteredChartBlock]
  exact parameterConstantCoeff_rightRecenteredHessianFourBlock
    C.chartData.chart.rho B.aligned.endpoint

/-- In a swap chart the Stage-3 special four-block is the swap of the
coordinate-permuted honest special Hessian. -/
theorem specialFourBlock_eq_swap02_coordinateSpecialFourBlock_of_swap02
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hkind : C.chartData.chart.kind =
      AdaptiveAlignedRightRecenteredHessianChartKind.swap02) :
    C.specialFourBlock = C.coordinateSpecialFourBlock.swap02 := by
  unfold specialFourBlock coordinateSpecialFourBlock
  rw [C.schurBlock_eq_chartBlock]
  unfold AdaptiveAlignedRightRecenteredExactHessianChart.block
  rw [hkind]
  simp only [adaptiveAlignedRightRecenteredChartBlock]
  rw [parameterConstantCoeffFourBlock_swap02]
  rw [parameterConstantCoeff_rightRecenteredHessianFourBlock]

/-- In a shear chart the Stage-3 special four-block is the shear of the
coordinate-permuted honest special Hessian. -/
theorem specialFourBlock_eq_shear02_coordinateSpecialFourBlock_of_shear02
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hkind : C.chartData.chart.kind =
      AdaptiveAlignedRightRecenteredHessianChartKind.shear02) :
    C.specialFourBlock = C.coordinateSpecialFourBlock.shear02 := by
  unfold specialFourBlock coordinateSpecialFourBlock
  rw [C.schurBlock_eq_chartBlock]
  unfold AdaptiveAlignedRightRecenteredExactHessianChart.block
  rw [hkind]
  simp only [adaptiveAlignedRightRecenteredChartBlock]
  rw [parameterConstantCoeffFourBlock_shear02]
  rw [parameterConstantCoeff_rightRecenteredHessianFourBlock]

/-- Nonzero polynomial kernel data on the honest coordinate-permuted special
Hessian, with the auxiliary swap/shear completely removed. -/
structure CoordinateSpecialKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  vector : Fin 4 → MvPolynomial (Fin 4) K
  vector_ne_zero : vector ≠ 0
  kernel : C.coordinateSpecialFourBlock.matrix.mulVec vector = 0

/-- The literal vector transform which removes the auxiliary Stage-3
coordinate/swap/shear chart.  Keeping this part nondependent makes later
projective-wedge transport transparent to simplification. -/
def coordinateKernelVectorForChartKind
    (kind : AdaptiveAlignedRightRecenteredHessianChartKind)
    (w : Fin 4 → MvPolynomial (Fin 4) K) :
    Fin 4 → MvPolynomial (Fin 4) K :=
  match kind with
  | .coordinate => w
  | .swap02 => swap02KernelVector w
  | .shear02 => shear02KernelVector w

namespace DenominatorClearedSpecialSchurKernelData

/-- The denominator-cleared Stage-3 kernel can always be transported through
the retained swap/shear to the coordinate-permuted honest special Hessian.
No source information and no nonzeroness is lost. -/
noncomputable def toCoordinateSpecialKernelData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : C.DenominatorClearedSpecialSchurKernelData) :
    C.CoordinateSpecialKernelData := by
  refine {
    vector := coordinateKernelVectorForChartKind
      C.chartData.chart.kind D.fullVector
    vector_ne_zero := ?_
    kernel := ?_
  }
  · intro hz
    generalize hkind : C.chartData.chart.kind = kind at hz
    cases kind with
    | coordinate =>
        apply D.fullVector_ne_zero
        simpa [coordinateKernelVectorForChartKind, hkind] using hz
    | swap02 =>
        apply D.fullVector_ne_zero
        apply swap02KernelVector_injective (R := MvPolynomial (Fin 4) K)
        simpa [coordinateKernelVectorForChartKind, hkind] using hz
    | shear02 =>
        apply D.fullVector_ne_zero
        apply shear02KernelVector_injective (R := MvPolynomial (Fin 4) K)
        simpa [coordinateKernelVectorForChartKind, hkind] using hz
  · generalize hkind : C.chartData.chart.kind = kind
    cases kind with
    | coordinate =>
        have hker := D.fullVector_kernel
        rw [C.specialFourBlock_eq_coordinateSpecialFourBlock_of_coordinate hkind]
          at hker
        simpa [coordinateKernelVectorForChartKind, hkind] using hker
    | swap02 =>
        have hker := D.fullVector_kernel
        rw [C.specialFourBlock_eq_swap02_coordinateSpecialFourBlock_of_swap02 hkind]
          at hker
        simpa [coordinateKernelVectorForChartKind, hkind] using
          C.coordinateSpecialFourBlock.mulVec_swap02KernelVector_eq_zero
            D.fullVector hker
    | shear02 =>
        have hker := D.fullVector_kernel
        rw [C.specialFourBlock_eq_shear02_coordinateSpecialFourBlock_of_shear02 hkind]
          at hker
        simpa [coordinateKernelVectorForChartKind, hkind] using
          C.coordinateSpecialFourBlock.mulVec_shear02KernelVector_eq_zero
            D.fullVector hker

end DenominatorClearedSpecialSchurKernelData

/-- Every early-Schur closing carrier therefore has a nonzero kernel of the
coordinate-permuted honest special-fibre Hessian. -/
theorem exists_coordinateSpecialKernelData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    Nonempty C.CoordinateSpecialKernelData := by
  rcases C.exists_denominatorClearedSpecialSchurKernelData with ⟨D⟩
  exact ⟨D.toCoordinateSpecialKernelData⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
