import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactQuadraticRees
import HC4.Valuation.PermutedFamilyHessianFourBlock
import Mathlib.Tactic

/-!
# A19.120: exact cleared-Schur clock for the contact Rees

The contact reverse Rees has genuine Hessian determinant `X^Delta`, with

    Delta = 4 * D - 2 * (contactGap + 4).

For any simultaneous source-coordinate permutation, the state-free four-block
from `PermutedFamilyHessianFourBlock` retains exactly this determinant clock.
The denominator-cleared general Schur identity then gives

    schurDetCore = activeDet * X^Delta.

This is the algebraic bridge needed by the other-facet profile calculation: no
inverse of the active block is taken, so A19.118's nonzero active pivot can be
used later purely to orient/identify the honest binary block.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The actual contact reverse-Rees family carried by the A19.112 package. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.contactFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  reverseWeightedReesFamily
    (qsIntegralContactWeight P.contactGap) T.topFace.degree
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) P.bound

/-- Every coordinate-permuted cleared Schur block of the contact family has the
same exact determinant clock. -/
theorem QsOtherFacetContactQuadraticReesPackage.permutedSchurDetCore_eq_activeDet_mul_X_pow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    let H := permutedFamilyHessianFourBlock rho P.contactFamily
    H.schurDetCore =
      H.activeDet *
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          (4 * T.topFace.degree - 2 * (P.contactGap + 4)) := by
  dsimp only
  rw [GeneralFourBlock.schurDetCore_eq_activeDet_mul_determinantCore]
  rw [permutedFamilyHessianFourBlock_determinantCore_eq_X_pow
    rho P.contactFamily P.hessianDefect]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
