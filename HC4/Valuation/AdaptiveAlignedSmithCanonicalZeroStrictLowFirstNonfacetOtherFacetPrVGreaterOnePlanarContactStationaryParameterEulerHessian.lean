import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryWeightedEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import Mathlib.Tactic

/-!
# A19 falling parameter row for the stationary ramified family

The stationary weighted-Euler identity is

    E_tau Q + r Q = r E_0 Q + r E_1 Q.

Applying the parameter Euler operator once more gives the mixed parameter/source
row needed by the stationary profile Hessian.  The only bookkeeping point is
that the family-level falling operator is `E_tau(E_tau-1)`, hence

    E_tau(E_tau Q) = E_tau(E_tau-1)Q + E_tau Q.

All identities in this module are ordinary polynomial differentiation facts;
no geometric hypothesis beyond the already-proved stationary weighted-Euler
equation is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K]

/-- Iterating the family parameter Euler operator is the falling second Euler
operator plus the first Euler operator. -/
theorem familyParameterEuler_familyParameterEuler
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    familyParameterEuler (familyParameterEuler Q) =
      familyParameterSecondEuler Q + familyParameterEuler Q := by
  apply MvPolynomial.ext
  intro e
  rw [coeff_familyParameterEuler, coeff_familyParameterEuler,
    coeff_familyParameterSecondEuler, MvPolynomial.coeff_add,
    coeff_familyParameterEuler]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X, one_mul]
  ring

/-- The family parameter Euler operator is additive. -/
theorem familyParameterEuler_add
    (A B : MvPolynomial (Fin 4) (Polynomial K)) :
    familyParameterEuler (A + B) =
      familyParameterEuler A + familyParameterEuler B := by
  apply MvPolynomial.ext
  intro e
  rw [coeff_familyParameterEuler, coeff_familyParameterEuler,
    coeff_familyParameterEuler, MvPolynomial.coeff_add,
    MvPolynomial.coeff_add, Polynomial.derivative_add]
  ring

/-- A ground-field scalar is constant in the family parameter, so parameter
Euler differentiation commutes with scalar multiplication. -/
theorem familyParameterEuler_groundScalar_mul
    (a : K)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    familyParameterEuler
        (MvPolynomial.C (Polynomial.C a) * Q) =
      MvPolynomial.C (Polynomial.C a) * familyParameterEuler Q := by
  apply MvPolynomial.ext
  intro e
  rw [coeff_familyParameterEuler, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C_mul, coeff_familyParameterEuler]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
    zero_mul, zero_add]
  ring

variable [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- **Falling stationary parameter row.**  Applying parameter Euler to
`E_tau Q + rQ = rE_0Q + rE_1Q` gives

`E_tau(E_tau-1)Q + (r+1)E_tau Q = r E_tau(E_0Q) + r E_tau(E_1Q)`.
-/
theorem stationaryRamifiedFamily_fallingParameterRow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterSecondEuler D.stationaryRamifiedFamily +
        MvPolynomial.C
          (Polynomial.C ((F.stationaryWeight : K) + 1)) *
          familyParameterEuler D.stationaryRamifiedFamily =
      MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4)
              D.stationaryRamifiedFamily) +
        MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          familyParameterEuler
            (HC4.Polynomial.mvEuler (1 : Fin 4)
              D.stationaryRamifiedFamily) := by
  have h := congrArg familyParameterEuler
    (D.stationaryRamifiedFamily_weightedEuler hthree houtThree)
  rw [familyParameterEuler_add,
    familyParameterEuler_groundScalar_mul,
    familyParameterEuler_add,
    familyParameterEuler_groundScalar_mul,
    familyParameterEuler_groundScalar_mul,
    familyParameterEuler_familyParameterEuler] at h
  linear_combination h

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
