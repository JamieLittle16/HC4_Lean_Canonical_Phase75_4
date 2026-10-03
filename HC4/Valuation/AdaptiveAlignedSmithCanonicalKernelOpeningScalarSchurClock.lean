import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningScalarPivot
import HC4.Newton.ScalarPivotThreeSchurClock
import Mathlib.Tactic

/-!
# A18.4.94: exact scalar-Schur clock on the genuine rank-one opening

A18.4.91 chooses a scalar Hessian pivot with nonzero constant coefficient on
the actual post-opening state.  Since A18.4.90 also proves that every
special-fibre `2 x 2` Hessian minor vanishes, all six entries of the cleared
`1+3` Schur block have zero constant coefficient.

A18.4.92 gives

    det S = a^2 det H,

and the scale-aware state already has `det H = X^Delta`.  Hence the scalar
Schur block is an `ExactScalarSchurThreeClock` with clearing factor `a^2`.
The first-entry residual defect is therefore a strictly smaller natural
number by A18.4.93.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Constant coefficient commutes with the cleared scalar-Schur `3 x 3`
construction. -/
theorem parameterConstantCoeff_scalarSchurThreeMatrix
    (H : GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K))) :
    (fun i j => (H.scalarSchurThreeMatrix i j).coeff 0) =
      (parameterConstantCoeffFourBlock H).scalarSchurThreeMatrix := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralFourBlock.scalarSchurThreeMatrix,
      GeneralFourBlock.scalarSchur11, GeneralFourBlock.scalarSchur12,
      GeneralFourBlock.scalarSchur13, GeneralFourBlock.scalarSchur22,
      GeneralFourBlock.scalarSchur23, GeneralFourBlock.scalarSchur33,
      parameterConstantCoeffFourBlock,
      Polynomial.coeff_zero_eq_eval_zero]

/-- All-minors-zero is invariant under the coordinate permutation used to
place the scalar pivot in position zero. -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry.allTwoByTwo_permuted
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source)
    (rho : Equiv.Perm (Fin 4)) :
    (parameterConstantCoeffFourBlock
      (scaleAwareHessianFourBlock rho G.firstContact.opening)).AllTwoByTwoMinorsZero := by
  let F := polynomialFamilySpecialFiber G.firstContact.opening.family
  let T := parameterConstantCoeffFourBlock
    (scaleAwareHessianFourBlock rho G.firstContact.opening)
  have hT :
      T = GeneralFourBlock.ofSymmetricMatrix
        (fun i j => HC4.Polynomial.hessian F (rho i) (rho j)) := by
    ext <;>
      simp [T, F, parameterConstantCoeffFourBlock,
        scaleAwareHessianFourBlock, GeneralFourBlock.ofSymmetricMatrix,
        scaleAwareHessianSeriesMatrix_coeff_zero]
  have hsym :
      ∀ i j : Fin 4,
        HC4.Polynomial.hessian F (rho i) (rho j) =
          HC4.Polynomial.hessian F (rho j) (rho i) := by
    intro i j
    change
      MvPolynomial.pderiv (rho j) (MvPolynomial.pderiv (rho i) F) =
        MvPolynomial.pderiv (rho i) (MvPolynomial.pderiv (rho j) F)
    exact (pderiv_comm_backport (rho i) (rho j) F).symm
  have hmatrix :
      T.matrix =
        fun i j => HC4.Polynomial.hessian F (rho i) (rho j) := by
    rw [hT]
    exact GeneralFourBlock.matrix_ofSymmetricMatrix _ hsym
  unfold GeneralFourBlock.AllTwoByTwoMinorsZero
  intro i j k l
  have h := G.allTwoByTwo (rho i) (rho j) (rho k) (rho l)
  rw [scaleAwareSpecialHessianFourBlock_matrix G.firstContact.opening] at h
  change T.matrix i j * T.matrix k l - T.matrix i l * T.matrix k j = 0
  rw [hmatrix]
  exact h

/-- Exact scalar-Schur clock attached to one chosen pivot. -/
structure AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) : Type (u + 1) where
  pivot : AdaptiveAlignedSmithCanonicalKernelOpeningScalarPivot G
  block : GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K))
  block_eq :
    block = scaleAwareHessianFourBlock pivot.permutation G.firstContact.opening
  clock : ExactScalarSchurThreeClock (MvPolynomial (Fin 4) K)
  clock_series_eq : clock.zeroSeries.series = block.scalarSchurThreeMatrix
  clock_defect_eq : clock.defect = G.firstContact.opening.rawDefect
  clock_clearing_eq : clock.clearingFactor = block.a ^ 2

/-- **Every genuine rank-one opening carries the exact integer scalar-Schur
clock.** -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry.scalarSchurClock
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) :
    Nonempty (AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) := by
  rcases G.scalarPivot with ⟨P⟩
  let s := G.firstContact.opening
  let H := scaleAwareHessianFourBlock P.permutation s
  let H0 := parameterConstantCoeffFourBlock H
  have hall0 : H0.AllTwoByTwoMinorsZero := by
    simpa [H, H0, s] using G.allTwoByTwo_permuted P.permutation
  have hschur0 : H0.scalarSchurThreeMatrix = 0 :=
    H0.scalarSchurThreeMatrix_eq_zero_of_allTwoByTwoMinorsZero
      (by
        simpa [GeneralFourBlock.AllTwoByTwoMinorsZero] using hall0)
  let Z : ZeroScalarSchurThreeSeries (MvPolynomial (Fin 4) K) := {
    series := H.scalarSchurThreeMatrix
    constant_zero := by
      intro i j
      have hmap := congrFun
        (congrFun (parameterConstantCoeff_scalarSchurThreeMatrix H) i) j
      have hz := congrFun (congrFun hschur0 i) j
      simpa using hmap.trans hz
  }
  have hclear : (H.a ^ 2).coeff 0 ≠ 0 := by
    have ha : H.a.coeff 0 ≠ 0 := by
      simpa [H, s] using P.pivot_coeff_zero_ne_zero
    simpa [Polynomial.coeff_zero_eq_eval_zero] using pow_ne_zero 2 ha
  have hdet :
      Z.series.det =
        H.a ^ 2 * Polynomial.X ^ s.rawDefect := by
    dsimp [Z]
    rw [GeneralFourBlock.scalarSchurThreeMatrix_det]
    rw [show H.determinantCore = Polynomial.X ^ s.rawDefect by
      simpa [H, s] using
        scaleAwareHessianFourBlock_determinantCore P.permutation s]
  let E : ExactScalarSchurThreeClock (MvPolynomial (Fin 4) K) := {
    zeroSeries := Z
    clearingFactor := H.a ^ 2
    defect := s.rawDefect
    clearingFactor_coeff_zero_ne_zero := hclear
    determinantFactor := hdet
  }
  exact ⟨{
    pivot := P
    block := H
    block_eq := rfl
    clock := E
    clock_series_eq := rfl
    clock_defect_eq := rfl
    clock_clearing_eq := rfl
  }⟩

/-- The first scalar-Schur re-entry strictly lowers the integral residual
Hessian determinant clock. -/
theorem AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock.residualDefect_lt
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source}
    (D : AdaptiveAlignedSmithCanonicalKernelOpeningScalarSchurClock G) :
    D.clock.residualDefect < G.firstContact.opening.rawDefect := by
  rw [← D.clock_defect_eq]
  exact D.clock.residualDefect_lt

end

end HC4.Valuation
