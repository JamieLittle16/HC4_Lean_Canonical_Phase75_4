import HC4.Valuation.AdaptiveAlignedSmithCanonicalActualRankTwoToRankThree
import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianShearCharts
import Mathlib.Tactic

/-!
# A18.4.88: rank-three consumer for any exact active Hessian four-block

A18.4.84 consumes a coordinate-permuted Hessian chart whose active `2 x 2`
special-fibre minor is nonzero.  For the final kernel-opening audit we also
need determinant-one shear charts: a symmetric matrix may have no nonzero
coordinate-principal `2 x 2` minor while a cross minor is nonzero.

The Schur argument itself uses only three facts:

* the block comes from the genuine state Hessian by an explicit permitted
  basis operation;
* its full determinant is exactly `X ^ rawDefect`; and
* its active determinant has nonzero constant coefficient.

This file packages those facts and repeats the A18.4.84 exhaustion once.  The
origin field prevents an unrelated algebraic four-block from being attached
to a state: every chart is either a simultaneous coordinate permutation of
the genuine Hessian or the explicit determinant-one `e_0 -> e_0 + e_2`
shear of such a permutation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Provenance of an exact active four-block on a scale-aware state. -/
inductive AdaptiveAlignedSmithCanonicalExactActiveFourBlockOrigin
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (H : GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K))) : Prop
  | direct
      (rho : Equiv.Perm (Fin 4))
      (block_eq : H = scaleAwareHessianFourBlock rho s)
  | shear02
      (rho : Equiv.Perm (Fin 4))
      (block_eq : H = (scaleAwareHessianFourBlock rho s).shear02)

/-- An honest state Hessian chart with an invertible active special-fibre
`2 x 2` block. -/
structure AdaptiveAlignedSmithCanonicalExactActiveFourBlock
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  block : GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K))
  origin : AdaptiveAlignedSmithCanonicalExactActiveFourBlockOrigin s block
  fullDet : block.determinantCore = Polynomial.X ^ s.rawDefect
  activeDet_coeff_zero_ne_zero : block.activeDet.coeff 0 ≠ 0

namespace AdaptiveAlignedSmithCanonicalExactActiveFourBlock

/-- Every old direct actual-rank-two chart is an exact active four-block. -/
noncomputable def ofDirect
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart s) :
    AdaptiveAlignedSmithCanonicalExactActiveFourBlock s where
  block := scaleAwareHessianFourBlock C.permutation s
  origin := .direct C.permutation rfl
  fullDet := C.fullDet
  activeDet_coeff_zero_ne_zero := C.activeDet_coeff_zero_ne_zero

/-- A nonzero active determinant after the explicit determinant-one shear is
an equally honest chart. -/
noncomputable def ofShear02
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (rho : Equiv.Perm (Fin 4))
    (hactive :
      ((scaleAwareHessianFourBlock rho s).shear02).activeDet.coeff 0 ≠ 0) :
    AdaptiveAlignedSmithCanonicalExactActiveFourBlock s where
  block := (scaleAwareHessianFourBlock rho s).shear02
  origin := .shear02 rho rfl
  fullDet := by
    rw [GeneralFourBlock.shear02_determinantCore]
    exact scaleAwareHessianFourBlock_determinantCore rho s
  activeDet_coeff_zero_ne_zero := hactive

end AdaptiveAlignedSmithCanonicalExactActiveFourBlock

/-- An actual nonzero constant `3 x 3` minor of an exact active block. -/
inductive AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalExactActiveFourBlock s) : Prop
  | first (hne : C.block.schurA.coeff 0 ≠ 0)
  | mixed (hne : C.block.schurB.coeff 0 ≠ 0)
  | second (hne : C.block.schurC.coeff 0 ≠ 0)

namespace AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry

/-- The three Schur numerators remain literal `3 x 3` determinants for the
possibly-sheared honest block. -/
theorem actualMinor
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {C : AdaptiveAlignedSmithCanonicalExactActiveFourBlock s}
    (G : AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry C) :
    C.block.firstThreeMinorMatrix.det.coeff 0 ≠ 0 ∨
      C.block.mixedThreeMinorMatrix.det.coeff 0 ≠ 0 ∨
      C.block.secondThreeMinorMatrix.det.coeff 0 ≠ 0 := by
  cases G with
  | first hne =>
      left
      simpa [GeneralFourBlock.firstThreeMinorMatrix_det] using hne
  | mixed hne =>
      right
      left
      simpa [GeneralFourBlock.mixedThreeMinorMatrix_det] using hne
  | second hne =>
      right
      right
      simpa [GeneralFourBlock.secondThreeMinorMatrix_det] using hne

end AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry

/-- Complete rank-three geometry carried by an arbitrary honest active chart. -/
inductive AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalExactActiveFourBlock s)
    (complexity : ℕ) : Type (u + 1)
  | constantMinor
      (G : AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry C)
      (rankTwoToRankThree :
        RepairProgress
          (rankTwoRepairState complexity)
          (rankThreeRepairState complexity))
  | zeroSchur
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (Z_block_eq : Z.block = C.block)
      (G : AdaptiveAlignedSmithCanonicalCompleteSourceRankThreeGeometry
        Z complexity)

/-- **Any honest exact active four-block has complete rank-three geometry.** -/
noncomputable def
    AdaptiveAlignedSmithCanonicalExactActiveFourBlock.rankThreeGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (C : AdaptiveAlignedSmithCanonicalExactActiveFourBlock s)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry C complexity := by
  let H := C.block
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
