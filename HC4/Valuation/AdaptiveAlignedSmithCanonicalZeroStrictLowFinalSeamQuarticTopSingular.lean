import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamQuarticEuler
import HC4.MongeAmpere.MaximalInitial
import Mathlib.Tactic

/-!
# G26: the quartic top homogeneous layer has singular Hessian

For the midpoint quartic core

    F = q2 + h3 + h4

we already know det Hess(F) = 1, with q2, h3 and h4 homogeneous of ordinary
degrees 2, 3 and 4.

Take the maximal ordinary initial form with weight (1,1,1,1) and level 4.
The determinant weight is

    4*4 - 2*(1+1+1+1) = 8 > 0.

The maximal-initial Monge--Ampere theorem therefore forces the Hessian
determinant of the level-four initial form to vanish.  That initial form is
exactly h4.

Hence

    det Hess(h4) = 0.

This is the precise homogeneous singular top required by the four-variable
Hesse/cone analysis.  No Hesse classification and no JC2 input is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Ordinary natural homogeneity is the same as weighted homogeneity for the
four-variable all-ones integer weight. -/
theorem isWeightedHomogeneous_fourOrdinary_of_isHomogeneous
    (P : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hhom : P.IsHomogeneous D) :
    P.IsWeightedHomogeneous fourOrdinaryIntegerWeight (D : ℤ) := by
  intro d hdcoeff
  rw [fourOrdinaryIntegerWeight_eq_ordinaryDegree4]
  have hdmem : d ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr hdcoeff
  exact_mod_cast ordinaryDegree4_eq_of_isHomogeneous hhom hdmem

/-- A degree-D homogeneous polynomial with D <= 4 has ordinary weight at most
four. -/
theorem isWeightLE_fourOrdinary_four_of_isHomogeneous_le
    (P : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hhom : P.IsHomogeneous D)
    (hD : D ≤ 4) :
    IsWeightLE fourOrdinaryIntegerWeight (4 : ℤ) P := by
  intro d hd
  rw [fourOrdinaryIntegerWeight_eq_ordinaryDegree4]
  have hdeg := ordinaryDegree4_eq_of_isHomogeneous hhom hd
  rw [hdeg]
  exact_mod_cast hD

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- The exact ordinary level-four initial form of the quartic core is h4. -/
theorem FinalSeamQuarticHomogeneousCoreData.initialForm_four_eq_h4
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : T.FinalSeamQuarticHomogeneousCoreData) :
    initialForm fourOrdinaryIntegerWeight (4 : ℤ)
        (C.q2 + C.h3 + C.h4) =
      C.h4 := by
  have hq2W :=
    isWeightedHomogeneous_fourOrdinary_of_isHomogeneous
      (K := K) C.q2 2 C.q2_homogeneous
  have h3W :=
    isWeightedHomogeneous_fourOrdinary_of_isHomogeneous
      (K := K) C.h3 3 C.h3_homogeneous
  have h4W :=
    isWeightedHomogeneous_fourOrdinary_of_isHomogeneous
      (K := K) C.h4 4 C.h4_homogeneous
  have hq2zero :
      initialForm fourOrdinaryIntegerWeight (4 : ℤ) C.q2 = 0 := by
    exact initialForm_eq_zero_of_isWeightedHomogeneous
      hq2W 4 (by norm_num)
  have h3zero :
      initialForm fourOrdinaryIntegerWeight (4 : ℤ) C.h3 = 0 := by
    exact initialForm_eq_zero_of_isWeightedHomogeneous
      h3W 4 (by norm_num)
  have h4self :
      initialForm fourOrdinaryIntegerWeight (4 : ℤ) C.h4 = C.h4 :=
    initialForm_eq_self_of_isWeightedHomogeneous h4W
  rw [initialForm_add, initialForm_add, hq2zero, h3zero, h4self]
  simp

/-- **Singular quartic top.**

The degree-four homogeneous component of every quartic final-seam core has
identically zero Hessian determinant. -/
theorem FinalSeamQuarticHomogeneousCoreData.h4_hessianDeterminant_eq_zero
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (C : T.FinalSeamQuarticHomogeneousCoreData) :
    HC4.Polynomial.hessianDeterminant C.h4 = 0 := by
  let F : MvPolynomial (Fin 4) K := C.q2 + C.h3 + C.h4
  have hq2LE :
      IsWeightLE fourOrdinaryIntegerWeight (4 : ℤ) C.q2 :=
    isWeightLE_fourOrdinary_four_of_isHomogeneous_le
      (K := K) C.q2 2 C.q2_homogeneous (by omega)
  have h3LE :
      IsWeightLE fourOrdinaryIntegerWeight (4 : ℤ) C.h3 :=
    isWeightLE_fourOrdinary_four_of_isHomogeneous_le
      (K := K) C.h3 3 C.h3_homogeneous (by omega)
  have h4LE :
      IsWeightLE fourOrdinaryIntegerWeight (4 : ℤ) C.h4 :=
    isWeightLE_fourOrdinary_four_of_isHomogeneous_le
      (K := K) C.h4 4 C.h4_homogeneous (by omega)
  have hFLE :
      IsWeightLE fourOrdinaryIntegerWeight (4 : ℤ) F := by
    dsimp [F]
    exact (hq2LE.add h3LE).add h4LE
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F := by
    exact C.hessianDet_one
  have hpos :
      0 <
        (Fintype.card (Fin 4) : ℤ) * 4 -
          2 * ∑ i : Fin 4, fourOrdinaryIntegerWeight i := by
    simp [fourOrdinaryIntegerWeight, Fin.sum_univ_four]
  have htop :=
    HC4.MongeAmpere.maximal_initial_hessianDeterminant_eq_zero
      fourOrdinaryIntegerWeight (4 : ℤ) F hFLE hMA hpos
  have hinit :
      initialForm fourOrdinaryIntegerWeight (4 : ℤ) F = C.h4 := by
    dsimp [F]
    exact C.initialForm_four_eq_h4
  rw [hinit] at htop
  exact htop

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
