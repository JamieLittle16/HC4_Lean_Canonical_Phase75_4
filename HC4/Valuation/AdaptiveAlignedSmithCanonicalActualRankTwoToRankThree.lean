import HC4.Valuation.AdaptiveAlignedSmithCanonicalSourceZeroSchurRankThree
import Mathlib.Tactic

/-!
# A18.4.84: any actual rank-two Hessian chart carries rank-three geometry

Let the active `2 x 2` special-fibre Hessian minor be nonzero.  The three
cleared Schur numerators `A,B,C` have an elementary determinantal meaning:

* `A` is the principal `3 x 3` minor using the first complementary coordinate;
* `B` is the mixed `3 x 3` minor using the other complementary column;
* `C` is the principal `3 x 3` minor using the second complementary coordinate.

Hence a nonzero constant coefficient of any Schur numerator is already an
actual rank-three Hessian event.

If all three constant coefficients vanish, then determinant order zero is
impossible by the cleared Schur determinant identity and the nonzero active
minor.  At positive determinant order the four-block is exact zero-Schur data,
and A18.4.83 supplies complete later rank-three geometry.

Thus an actual rank-two chart never needs a repair-only `2 -> 3` relabel: the
third direction is always retained explicitly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace GeneralFourBlock

variable {R : Type*} [CommRing R]

/-- Principal `3 x 3` minor adjoining the first complementary coordinate. -/
def firstThreeMinorMatrix (H : GeneralFourBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![H.a, H.b, H.p;
     H.b, H.d, H.r;
     H.p, H.r, H.x]

/-- Mixed `3 x 3` minor with active rows/columns and the two different
complementary directions. -/
def mixedThreeMinorMatrix (H : GeneralFourBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![H.a, H.b, H.q;
     H.b, H.d, H.s;
     H.p, H.r, H.y]

/-- Principal `3 x 3` minor adjoining the second complementary coordinate. -/
def secondThreeMinorMatrix (H : GeneralFourBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![H.a, H.b, H.q;
     H.b, H.d, H.s;
     H.q, H.s, H.z]

/-- The first cleared Schur numerator is literally the first principal
`3 x 3` determinant. -/
theorem firstThreeMinorMatrix_det (H : GeneralFourBlock R) :
    H.firstThreeMinorMatrix.det = H.schurA := by
  simp [firstThreeMinorMatrix, GeneralFourBlock.schurA,
    GeneralFourBlock.activeDet, Matrix.det_fin_three]
  ring

/-- The off-diagonal cleared Schur numerator is literally a mixed `3 x 3`
minor. -/
theorem mixedThreeMinorMatrix_det (H : GeneralFourBlock R) :
    H.mixedThreeMinorMatrix.det = H.schurB := by
  simp [mixedThreeMinorMatrix, GeneralFourBlock.schurB,
    GeneralFourBlock.activeDet, Matrix.det_fin_three]
  ring

/-- The second cleared Schur numerator is the second principal `3 x 3`
determinant. -/
theorem secondThreeMinorMatrix_det (H : GeneralFourBlock R) :
    H.secondThreeMinorMatrix.det = H.schurC := by
  simp [secondThreeMinorMatrix, GeneralFourBlock.schurC,
    GeneralFourBlock.activeDet, Matrix.det_fin_three]
  ring

end GeneralFourBlock

/-- An explicit nonzero constant `3 x 3` Hessian minor of a retained actual
rank-two chart. -/
inductive AdaptiveAlignedSmithCanonicalThreeByThreeMinorGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s) : Prop
  | first
      (hne :
        (scaleAwareHessianFourBlock C.permutation s).schurA.coeff 0 ≠ 0)
  | mixed
      (hne :
        (scaleAwareHessianFourBlock C.permutation s).schurB.coeff 0 ≠ 0)
  | second
      (hne :
        (scaleAwareHessianFourBlock C.permutation s).schurC.coeff 0 ≠ 0)

namespace AdaptiveAlignedSmithCanonicalThreeByThreeMinorGeometry

/-- Every constructor really is the constant coefficient of an actual
`3 x 3` minor determinant. -/
theorem actualMinor
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s}
    (G : AdaptiveAlignedSmithCanonicalThreeByThreeMinorGeometry C) :
    (∃ hne :
        (scaleAwareHessianFourBlock C.permutation s).firstThreeMinorMatrix.det.coeff 0 ≠ 0,
      True) ∨
    (∃ hne :
        (scaleAwareHessianFourBlock C.permutation s).mixedThreeMinorMatrix.det.coeff 0 ≠ 0,
      True) ∨
    (∃ hne :
        (scaleAwareHessianFourBlock C.permutation s).secondThreeMinorMatrix.det.coeff 0 ≠ 0,
      True) := by
  cases G with
  | first hne =>
      left
      refine ⟨?_, trivial⟩
      simpa [GeneralFourBlock.firstThreeMinorMatrix_det] using hne
  | mixed hne =>
      right
      left
      refine ⟨?_, trivial⟩
      simpa [GeneralFourBlock.mixedThreeMinorMatrix_det] using hne
  | second hne =>
      right
      right
      refine ⟨?_, trivial⟩
      simpa [GeneralFourBlock.secondThreeMinorMatrix_det] using hne

end AdaptiveAlignedSmithCanonicalThreeByThreeMinorGeometry

/-- Complete geometry which licenses a `rankTwo -> rankThree` repair on one
actual state. -/
inductive AdaptiveAlignedSmithCanonicalActualRankThreeGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s)
    (complexity : ℕ) : Type (u + 1)
  | constantMinor
      (G : AdaptiveAlignedSmithCanonicalThreeByThreeMinorGeometry C)
      (rankTwoToRankThree :
        RepairProgress
          (rankTwoRepairState complexity)
          (rankThreeRepairState complexity))
  | zeroSchur
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (Z_block_eq : Z.block = scaleAwareHessianFourBlock C.permutation s)
      (G : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        Z complexity)

/-- **Universal actual-rank-two -> rank-three geometry theorem.** -/
noncomputable def
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart.rankThreeGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalActualRankThreeGeometry C complexity := by
  let H := scaleAwareHessianFourBlock C.permutation s
  by_cases hzero :
      H.schurA.coeff 0 = 0 ∧
        H.schurB.coeff 0 = 0 ∧
        H.schurC.coeff 0 = 0
  · have hdefectPos : 0 < s.rawDefect := by
      by_contra hnot
      have hdefect0 : s.rawDefect = 0 := Nat.eq_zero_of_not_pos hnot
      have hschur :
          H.polynomialSchurSeries.determinant =
            H.activeDet * Polynomial.X ^ s.rawDefect := by
        calc
          H.polynomialSchurSeries.determinant =
              H.activeDet * H.determinantCore :=
            H.polynomialSchurSeries_determinant
          _ = H.activeDet * Polynomial.X ^ s.rawDefect := by
            rw [C.fullDet]
      have hcoeff := congrArg
        (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0) hschur
      have hleft : H.polynomialSchurSeries.determinant.coeff 0 = 0 := by
        simp [BinarySchurPolynomialSeries.determinant,
          GeneralFourBlock.polynomialSchurSeries, hzero]
      have hright : (H.activeDet * Polynomial.X ^ s.rawDefect).coeff 0 ≠ 0 := by
        rw [hdefect0]
        simpa using C.activeDet_coeff_zero_ne_zero
      exact (hright (by simpa [hleft] using hcoeff.symm)).elim
    let Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K) := {
      block := H
      defect := s.rawDefect
      fullDet := C.fullDet
      activeDet_coeff_zero_ne_zero := C.activeDet_coeff_zero_ne_zero
      schurA_coeff_zero := hzero.1
      schurB_coeff_zero := hzero.2.1
      schurC_coeff_zero := hzero.2.2
    }
    exact .zeroSchur Z rfl
      (exactSourceZeroSchur_completeRankThreeGeometry Z complexity)

  · have hsome :
        H.schurA.coeff 0 ≠ 0 ∨
          H.schurB.coeff 0 ≠ 0 ∨
          H.schurC.coeff 0 ≠ 0 := by
      tauto
    have hrepair := rankTwo_to_rankThree_repairProgress complexity
    rcases hsome with hA | hB | hC
    · exact .constantMinor (.first hA) hrepair
    · exact .constantMinor (.mixed hB) hrepair
    · exact .constantMinor (.second hC) hrepair

end

end HC4.Valuation
