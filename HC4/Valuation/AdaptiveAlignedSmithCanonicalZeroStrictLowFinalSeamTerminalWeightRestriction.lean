
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamTransverseSquare
import HC4.Valuation.AdaptiveAlignedSmithFirstContactUniqueZeroElimination
import Mathlib.Tactic

/-!
# G14: terminal weights on the final seam are forced into the two-zero side

G13 produces a determinant-one field-valued final-seam fibre with

* the exact marked collision `0 ~ -e_0`; and
* a literal transverse square `X_ell^2` in support, with `ell != 0`.

Suppose an honest terminal weight is supplied on this fibre: it is
non-scalar, nonnegative, weighted-homogeneous, and has the marked longitudinal
zero `lambda 0 = 0`.

The determinant-one identity makes the actual Hessian at the origin
nondegenerate, hence these hypotheses form a non-scalar terminal conformal
face.  If coordinate zero were the only zero weight, the already-green
one-zero marked-axis argument gives a contradiction.  Therefore a second
zero exists.

Moreover the supported square has weighted degree `d`, so
`2 * lambda ell = d`.  The terminal degree is positive, hence
`lambda ell > 0`.  The second zero is therefore different from both the
marked longitudinal coordinate and the transverse square coordinate.

This theorem does not construct the terminal weight.  It proves that any
honest extraction is automatically routed to the two-zero / planar side.
No JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The determinant-one G13 fibre has nondegenerate actual Hessian at the
source origin. -/
theorem FinalSeamTransverseSquareData.hasNondegenerateActualHessian
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (S : T.FinalSeamTransverseSquareData) :
    HasNondegenerateTerminalActualHessian
      (0 : Fin 4) 1 2 3 S.fibre := by
  unfold HasNondegenerateTerminalActualHessian
  have hmatrix :
      terminalActualHessianMatrix (0 : Fin 4) 1 2 3 S.fibre =
        quadraticFamilyHessianMatrix S.fibre := by
    ext i j
    unfold terminalActualHessianMatrix quadraticFamilyHessianMatrix
    simp only [terminalFourCoordinate_standard]
    unfold mvHessianComponentAt
    change
      MvPolynomial.eval (fun _ : Fin 4 => (0 : K))
          (MvPolynomial.pderiv i (MvPolynomial.pderiv j S.fibre)) =
        MvPolynomial.constantCoeff
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i S.fibre))
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]
    rw [pderiv_comm_commRing i j S.fibre]
  rw [hmatrix, quadraticFamilyHessianMatrix_det]
  rw [S.hessianDeterminant_one]
  simp

/-- The determinant-one G13 fibre is a polynomial Monge--Ampere potential. -/
theorem FinalSeamTransverseSquareData.mongeAmpere
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (S : T.FinalSeamTransverseSquareData) :
    HC4.MongeAmpere.IsPolynomialMongeAmpere S.fibre := by
  change HC4.Polynomial.hessianDeterminant S.fibre = 1
  exact S.hessianDeterminant_one

/-- A candidate honest terminal weight on the G13 fibre.  The only missing
part of the HC4-specific extraction is existence of such a weight. -/
structure FinalSeamMarkedTerminalWeight
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (S : T.FinalSeamTransverseSquareData) : Prop where
  lambda : Fin 4 → ℤ
  degree : ℤ
  nonScalar : IsNonScalarIntegralWeight lambda
  nonnegative : IsNonnegativeIntegralWeight lambda
  markedZero : lambda (0 : Fin 4) = 0
  homogeneous :
    IsIntegralWeightedHomogeneous lambda degree S.fibre

/-- Every candidate terminal weight is a genuine non-scalar conformal
terminal face, because the G13 fibre has nondegenerate actual Hessian. -/
theorem FinalSeamMarkedTerminalWeight.conformalFace
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {S : T.FinalSeamTransverseSquareData}
    (W : S.FinalSeamMarkedTerminalWeight) :
    HasNonScalarTerminalConformalFace
      (0 : Fin 4) 1 2 3 W.lambda W.degree S.fibre := by
  exact
    nonScalarTerminal_actualHessian_conformalFace
      (0 : Fin 4) 1 2 3
      W.nonScalar W.homogeneous S.hasNondegenerateActualHessian

/-- Coordinate zero cannot be the unique zero weight: that would standardize
to the one-zero terminal pattern while preserving the marked collision, which
is already contradictory. -/
theorem FinalSeamMarkedTerminalWeight.exists_second_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {S : T.FinalSeamTransverseSquareData}
    (W : S.FinalSeamMarkedTerminalWeight) :
    ∃ z : Fin 4, z ≠ 0 ∧ W.lambda z = 0 := by
  by_contra hnone
  push_neg at hnone
  have hunique :
      ∀ i : Fin 4, W.lambda i = 0 → i = 0 := by
    intro i hi
    by_contra hi0
    exact hnone i hi0 hi

  rcases
      uniqueZeroTerminalWeight_standardizes
        W.conformalFace W.nonnegative W.markedZero hunique with
    ⟨rho, a, hfix, ha, had, hweight⟩

  have hweightFun :
      (fun i : Fin 4 => W.lambda (rho.symm i)) =
        standardOneZeroTerminalWeight W.degree a := by
    funext i
    exact hweight i

  have hhomRenamed :
      IsIntegralWeightedHomogeneous
        (standardOneZeroTerminalWeight W.degree a)
        W.degree
        (MvPolynomial.rename rho S.fibre) := by
    have h :=
      integralWeightedHomogeneous_rename_perm W.homogeneous rho
    rw [hweightFun] at h
    exact h

  have hMARenamed :
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (MvPolynomial.rename rho S.fibre) :=
    isPolynomialMongeAmpere_rename_perm rho S.mongeAmpere

  have hcoll := S.exactCollision.rename_perm rho
  have hcollMarked :
      HasExactGradientCollision
        (MvPolynomial.rename rho S.fibre)
        (fun _ : Fin 4 => (0 : K))
        (negativeLongitudinalAxisPoint (K := K)) := by
    rw [terminalPermutePoint_zeroPoint] at hcoll
    rw [terminalPermutePoint_negativeLongitudinalAxis_of_fix_zero
      rho hfix] at hcoll
    simpa [negativeLongitudinalAxisPoint] using hcoll

  exact
    standardOneZero_negativeLongitudinalAxis_collision_impossible
      ha had hhomRenamed hMARenamed hcollMarked

/-- The distinguished transverse square coordinate has strictly positive
terminal weight. -/
theorem FinalSeamMarkedTerminalWeight.squareCoordinate_pos
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {S : T.FinalSeamTransverseSquareData}
    (W : S.FinalSeamMarkedTerminalWeight) :
    0 < W.lambda S.familyPacket.ell := by
  have hdpos :
      0 < W.degree :=
    nonnegative_nonScalar_terminal_degree_pos
      W.conformalFace W.nonnegative
  have hdeg :=
    W.homogeneous
      (HC4.Newton.quadraticExponent
        S.familyPacket.ell S.familyPacket.ell)
      S.squareCoeff_ne_zero
  have htwice :
      W.lambda S.familyPacket.ell +
          W.lambda S.familyPacket.ell =
        W.degree := by
    simpa [HC4.Newton.quadraticExponent,
      integralWeightedDegree_eq_finsuppWeight] using hdeg
  linarith

/-- **G14 terminal two-zero routing.**

Any honest marked terminal weight on the G13 fibre has a second zero away from
both coordinate zero and the transverse square coordinate. -/
theorem FinalSeamMarkedTerminalWeight.exists_second_zero_away_from_square
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {S : T.FinalSeamTransverseSquareData}
    (W : S.FinalSeamMarkedTerminalWeight) :
    ∃ z : Fin 4,
      z ≠ 0 ∧
      z ≠ S.familyPacket.ell ∧
      W.lambda z = 0 := by
  rcases W.exists_second_zero with ⟨z, hz0, hzw⟩
  refine ⟨z, hz0, ?_, hzw⟩
  intro hzell
  subst z
  have hpos := W.squareCoordinate_pos
  rw [hzw] at hpos
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
