import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningThreeTailFrontier
import Mathlib.Tactic

/-!
# A18.4.97: second scalar pivot produces an exact binary zero-Schur clock

The only residual branch of A18.4.96 has a nonzero rank-one constant `3 x 3`
first-tail matrix.  Choose one of its nonzero diagonal entries and permute it to
position zero.  The *entire polynomial first-tail matrix* is permuted in the
same way and packed as a `GeneralThreeBlock`.

Because every `2 x 2` minor of the constant tail vanishes, the cleared binary
Schur complement of that second scalar pivot has zero constant block.  The
A18.4.95 determinant identity gives

    det S_2 = a_2 * det T_1.

A18.4.93 already gives

    det T_1 = Q * X^delta_1,

and the selected second pivot has nonzero constant coefficient.  Therefore
`S_2` is exactly an `ExactZeroSchurClock` of defect `delta_1`.  This is the
existing green binary clock, so no new infinite rank recursion remains after
this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

private noncomputable def secondPivotSwap01 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

private noncomputable def secondPivotSwap02 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 2

@[simp] private theorem secondPivotSwap01_zero : secondPivotSwap01 0 = 1 := by decide
@[simp] private theorem secondPivotSwap01_one : secondPivotSwap01 1 = 0 := by decide
@[simp] private theorem secondPivotSwap01_two : secondPivotSwap01 2 = 2 := by decide

@[simp] private theorem secondPivotSwap02_zero : secondPivotSwap02 0 = 2 := by decide
@[simp] private theorem secondPivotSwap02_one : secondPivotSwap02 1 = 1 := by decide
@[simp] private theorem secondPivotSwap02_two : secondPivotSwap02 2 = 0 := by decide

/-- The full polynomial first-tail matrix is symmetric, not only its constant
coefficient.  Symmetry is inherited from the original scalar-Schur matrix by
cancelling the common nonzero first power of `X`. -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.tailMatrix_symmetric_secondZero
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    ∀ i j, D.clock.tailMatrix i j = D.clock.tailMatrix j i := by
  intro i j
  have hsymm :
      D.clock.zeroSeries.series i j = D.clock.zeroSeries.series j i := by
    rw [D.clock_series_eq]
    exact D.block.scalarSchurThreeMatrix_symmetric i j
  have hleft := D.clock.zeroSeries.entry_eq_firstFactor_mul_tail
    D.clock.hasPositiveEntryLayer i j
  have hright := D.clock.zeroSeries.entry_eq_firstFactor_mul_tail
    D.clock.hasPositiveEntryLayer j i
  have hscaled :
      Polynomial.X ^ D.clock.firstOrder * D.clock.tailMatrix i j =
        Polynomial.X ^ D.clock.firstOrder * D.clock.tailMatrix j i := by
    calc
      Polynomial.X ^ D.clock.firstOrder * D.clock.tailMatrix i j =
          D.clock.zeroSeries.series i j := hleft.symm
      _ = D.clock.zeroSeries.series j i := hsymm
      _ = Polynomial.X ^ D.clock.firstOrder * D.clock.tailMatrix j i := hright
  exact mul_left_cancel₀
    (pow_ne_zero D.clock.firstOrder Polynomial.X_ne_zero) hscaled

/-- Constant-coefficient specialization of a polynomial-valued three-block. -/
noncomputable def constantCoeffGeneralThreeBlock
    (T : GeneralThreeBlock (Polynomial (MvPolynomial (Fin 4) K))) :
    GeneralThreeBlock (MvPolynomial (Fin 4) K) where
  a := T.a.coeff 0
  b := T.b.coeff 0
  c := T.c.coeff 0
  d := T.d.coeff 0
  e := T.e.coeff 0
  f := T.f.coeff 0

/-- Constant coefficient commutes with the displayed three-block matrix. -/
theorem constantCoeffGeneralThreeBlock_matrix
    (T : GeneralThreeBlock (Polynomial (MvPolynomial (Fin 4) K))) :
    (constantCoeffGeneralThreeBlock T).matrix =
      fun i j => (T.matrix i j).coeff 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    rfl

/-- Constant coefficient commutes with the three cleared scalar-Schur entries. -/
theorem constantCoeffGeneralThreeBlock_scalarSchur
    (T : GeneralThreeBlock (Polynomial (MvPolynomial (Fin 4) K))) :
    T.scalarSchurA.coeff 0 = (constantCoeffGeneralThreeBlock T).scalarSchurA ∧
      T.scalarSchurB.coeff 0 = (constantCoeffGeneralThreeBlock T).scalarSchurB ∧
      T.scalarSchurC.coeff 0 = (constantCoeffGeneralThreeBlock T).scalarSchurC := by
  simp [GeneralThreeBlock.scalarSchurA, GeneralThreeBlock.scalarSchurB,
    GeneralThreeBlock.scalarSchurC, constantCoeffGeneralThreeBlock,
    Polynomial.coeff_zero_eq_eval_zero]

/-- Complete second-pivot binary clock with its polynomial three-block
provenance retained. -/
structure AdaptiveAlignedSmithCanonicalKernelOpeningSecondZeroSchurClock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (P : AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot G) : Type (u + 1) where
  permutation : Equiv.Perm (Fin 3)
  pivot_eq : permutation 0 = P.pivotIndex
  threeBlock : GeneralThreeBlock (Polynomial (MvPolynomial (Fin 4) K))
  threeBlock_matrix_eq :
    threeBlock.matrix = P.clock.clock.tailMatrix.submatrix permutation permutation
  zeroClock : ExactZeroSchurClock (MvPolynomial (Fin 4) K)
  defect_eq : zeroClock.defect = P.clock.clock.residualDefect
  clearing_eq :
    zeroClock.clearingFactor = threeBlock.a * P.clock.clock.clearingFactor

namespace AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot

/-- Build the second clock for a specified permutation carrying the selected
pivot to local coordinate zero. -/
noncomputable def toZeroSchurClockWithPermutation
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (P : AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot G)
    (rho : Equiv.Perm (Fin 3))
    (hrho : rho 0 = P.pivotIndex) :
    AdaptiveAlignedSmithCanonicalKernelOpeningSecondZeroSchurClock P := by
  let M := P.clock.clock.tailMatrix.submatrix rho rho
  have hsymmM : ∀ i j, M i j = M j i := by
    intro i j
    exact P.clock.tailMatrix_symmetric_secondZero (rho i) (rho j)
  let T := GeneralThreeBlock.ofSymmetricMatrix M hsymmM
  have hTmatrix : T.matrix = M :=
    GeneralThreeBlock.matrix_ofSymmetricMatrix M hsymmM

  let T0 := constantCoeffGeneralThreeBlock T
  have hT0matrix :
      T0.matrix = P.clock.clock.tailConstantMatrix.submatrix rho rho := by
    calc
      T0.matrix = fun i j => (T.matrix i j).coeff 0 :=
        constantCoeffGeneralThreeBlock_matrix T
      _ = fun i j => (M i j).coeff 0 := by rw [hTmatrix]
      _ = P.clock.clock.tailConstantMatrix.submatrix rho rho := by
        rfl

  have hall0 : T0.AllTwoByTwoMinorsZero := by
    unfold GeneralThreeBlock.AllTwoByTwoMinorsZero
    intro i j k l
    have h := P.allTwoByTwo (rho i) (rho j) (rho k) (rho l)
    rw [P.clock.tailThreeBlock_matrix] at h
    simpa [hT0matrix] using h

  have hschur0 := T0.scalarSchur_eq_zero_of_allTwoByTwoMinorsZero hall0
  have hcoeff := constantCoeffGeneralThreeBlock_scalarSchur T

  let Z : ZeroSchurSeries (MvPolynomial (Fin 4) K) := {
    series := {
      active := T.scalarSchurA
      offDiag := T.scalarSchurB
      kernel := T.scalarSchurC
    }
    active_coeff_zero := by simpa using hcoeff.1.trans hschur0.1
    offDiag_coeff_zero := by simpa using hcoeff.2.1.trans hschur0.2.1
    kernel_coeff_zero := by simpa using hcoeff.2.2.trans hschur0.2.2
  }

  have hpivot0 : T.a.coeff 0 ≠ 0 := by
    have hp : P.clock.clock.tailConstantMatrix P.pivotIndex P.pivotIndex ≠ 0 := by
      simpa [P.clock.tailThreeBlock_matrix, GeneralThreeBlock.matrix] using
        P.pivot_ne_zero
    have hlocal : P.clock.clock.tailConstantMatrix (rho 0) (rho 0) ≠ 0 := by
      simpa [hrho] using hp
    have hentry : T.a.coeff 0 =
        P.clock.clock.tailConstantMatrix (rho 0) (rho 0) := by
      have hm := congrFun (congrFun hT0matrix 0) 0
      simpa [T0, GeneralThreeBlock.matrix] using hm
    rw [hentry]
    exact hlocal

  have hclear :
      (T.a * P.clock.clock.clearingFactor).coeff 0 ≠ 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using
      mul_ne_zero hpivot0 P.clock.clock.clearingFactor_coeff_zero_ne_zero

  have hTdet :
      T.determinantCore = P.clock.clock.tailMatrix.det := by
    rw [← T.matrix_det, hTmatrix]
    exact Matrix.det_submatrix_equiv_self rho P.clock.clock.tailMatrix

  have hdet :
      Z.series.determinant =
        (T.a * P.clock.clock.clearingFactor) *
          Polynomial.X ^ P.clock.clock.residualDefect := by
    change T.scalarSchurDeterminant = _
    rw [T.scalarSchurDeterminant_eq, hTdet,
      P.clock.clock.tail_determinantFactor]
    ring

  let E : ExactZeroSchurClock (MvPolynomial (Fin 4) K) := {
    zeroSeries := Z
    clearingFactor := T.a * P.clock.clock.clearingFactor
    defect := P.clock.clock.residualDefect
    clearingFactor_coeff_zero_ne_zero := hclear
    determinantFactor := hdet
  }

  exact {
    permutation := rho
    pivot_eq := hrho
    threeBlock := T
    threeBlock_matrix_eq := hTmatrix
    zeroClock := E
    defect_eq := rfl
    clearing_eq := rfl
  }

/-- **Canonical second scalar-pivot binary zero-Schur clock.** -/
noncomputable def toZeroSchurClock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (P : AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot G) :
    AdaptiveAlignedSmithCanonicalKernelOpeningSecondZeroSchurClock P := by
  fin_cases h : P.pivotIndex
  · exact P.toZeroSchurClockWithPermutation (Equiv.refl (Fin 3)) (by simpa [h])
  · exact P.toZeroSchurClockWithPermutation secondPivotSwap01 (by simpa [h])
  · exact P.toZeroSchurClockWithPermutation secondPivotSwap02 (by simpa [h])

end AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot

end

end HC4.Valuation
