import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactQuadraticRees
import HC4.Valuation.BoundedReverseWeightedReesLayerSupport
import HC4.Valuation.FirstSchurDepartureBridge
import Mathlib.Tactic

/-!
# A19.113: every quadratic contact-Rees coefficient is preclosing

A19.112 gives the integral contact Rees the exact margin

    2*D < Delta.

Every source layer of a bounded reverse Rees occurs at parameter order at most
`D`.  Therefore the sum of any two actual source-layer orders is less than the
Hessian determinant clock.  More strongly, every determinant coefficient
through order `2*D` vanishes, whether or not that order itself occurs in the
source family.
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

/-- All full Hessian-determinant coefficients through twice the contact source
level vanish. -/
theorem QsOtherFacetContactQuadraticReesPackage.determinantLayer_zero_of_le_two_level
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    {n : ℕ}
    (hn : n ≤ 2 * T.topFace.degree) :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant
        (reverseWeightedReesFamily
          (qsIntegralContactWeight P.contactGap) T.topFace.degree
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) P.bound)) n = 0 := by
  exact hessianDefect_parameterLayer_eq_zero_of_lt
    (reverseWeightedReesFamily
      (qsIntegralContactWeight P.contactGap) T.topFace.degree
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) P.bound)
    P.hessianDefect (lt_of_le_of_lt hn P.two_level_lt_defect)

/-- Every actual contact-Rees source layer occurs no later than the contact
source level. -/
theorem QsOtherFacetContactQuadraticReesPackage.actualLayerOrder_le_level
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    {n : ℕ}
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily
        (qsIntegralContactWeight P.contactGap) T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) P.bound)) :
    n ≤ T.topFace.degree := by
  exact reverseWeightedReesFamily_actualLayerOrder_le_level
    (qsIntegralContactWeight P.contactGap) T.topFace.degree
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    P.bound hn

/-- The sum of any two actual contact-Rees source-layer orders is strictly
preclosing. -/
theorem QsOtherFacetContactQuadraticReesPackage.actualLayerPairOrder_lt_defect
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    {m n : ℕ}
    (hm : m ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily
        (qsIntegralContactWeight P.contactGap) T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) P.bound))
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily
        (qsIntegralContactWeight P.contactGap) T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) P.bound)) :
    m + n <
      4 * T.topFace.degree - 2 * (P.contactGap + 4) := by
  have hmD := P.actualLayerOrder_le_level hm
  have hnD := P.actualLayerOrder_le_level hn
  have hsum : m + n ≤ 2 * T.topFace.degree := by omega
  exact lt_of_le_of_lt hsum P.two_level_lt_defect

/-- Hence the full determinant coefficient at any pairwise actual-layer sum is
zero. -/
theorem QsOtherFacetContactQuadraticReesPackage.determinantLayer_zero_of_actualLayerPair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    {m n : ℕ}
    (hm : m ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily
        (qsIntegralContactWeight P.contactGap) T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) P.bound))
    (hn : n ∈ familyParameterLayerOrders
      (reverseWeightedReesFamily
        (qsIntegralContactWeight P.contactGap) T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) P.bound)) :
    familyParameterLayer
      (HC4.Polynomial.hessianDeterminant
        (reverseWeightedReesFamily
          (qsIntegralContactWeight P.contactGap) T.topFace.degree
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) P.bound))
      (m + n) = 0 := by
  exact hessianDefect_parameterLayer_eq_zero_of_lt
    (reverseWeightedReesFamily
      (qsIntegralContactWeight P.contactGap) T.topFace.degree
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) P.bound)
    P.hessianDefect (P.actualLayerPairOrder_lt_defect hm hn)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
