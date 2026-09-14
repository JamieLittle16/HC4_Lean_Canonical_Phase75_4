import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryCarrierEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import Mathlib.Tactic

/-!
# A19 second-order planar Euler equations on the stationary ramified family

The two affine Euler equations of the planar carrier are already available as
whole-family identities after stationary ramification.  The Schur/profile
adapter needs their falling second-order source rows.

For an affine support equation

    sum_j a_j e_j = d,

the Euler-scaled Hessian satisfies, coefficientwise,

    sum_j a_j H_{ij} = (d-a_i) E_i Q.

This module records that identity for the staircase wall and the monomial-curve
relation of the actual stationary ramified family.  The proof is source-honest:
outside the literal carrier support the ramified coefficient is zero, while on
support the already-proved scalar Euler equations are multiplied by the actual
coefficient.  No division, localization, or new homogeneity assumption is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

private theorem stationaryRamifiedFamily_coeff_eq_zero_of_not_carrier_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    {e : Fin 4 →₀ ℕ}
    (he : e ∉ P.carrier.support) :
    MvPolynomial.coeff e D.stationaryRamifiedFamily = 0 := by
  unfold stationaryRamifiedFamily parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  unfold QsOtherFacetPrLeftVPlanarContactReesData.family
  rw [reverseWeightedReesFamily_coeff]
  rw [if_neg he]
  simp

/-- **Falling staircase-wall source row.**  This is the Hessian-level form of
`stationaryRamifiedFamily_wallEuler`. -/
theorem stationaryRamifiedFamily_wallEulerRow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (i : Fin 4) :
    MvPolynomial.C
        (Polynomial.C (((F.highest.n : K) - 1) + (F.locked.ell : K))) *
        HC4.Polynomial.eulerScaledHessian
          D.stationaryRamifiedFamily i (0 : Fin 4) +
      MvPolynomial.C (Polynomial.C (F.locked.ell : K)) *
        HC4.Polynomial.eulerScaledHessian
          D.stationaryRamifiedFamily i (1 : Fin 4) +
      MvPolynomial.C (Polynomial.C ((F.highest.n : K) - 1)) *
        HC4.Polynomial.eulerScaledHessian
          D.stationaryRamifiedFamily i (2 : Fin 4) =
    MvPolynomial.C
        (Polynomial.C
          ((((F.highest.n : K) - 1) +
              (F.locked.ell : K) * (F.highest.n : K)) -
            (if i = (0 : Fin 4) then
                ((F.highest.n : K) - 1) + (F.locked.ell : K)
             else if i = (1 : Fin 4) then
                (F.locked.ell : K)
             else if i = (2 : Fin 4) then
                (F.highest.n : K) - 1
             else 0))) *
      HC4.Polynomial.mvEuler i D.stationaryRamifiedFamily := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_eulerScaledHessian, coeff_mvEuler]
  by_cases he : e ∈ P.carrier.support
  · have hs := F.support_wallEuler_scalar hthree houtThree he
    have hP := congrArg Polynomial.C hs
    have hnat (n : ℕ) :
        (n : Polynomial K) = Polynomial.C (n : K) :=
      (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
    rw [hnat (e 0), hnat (e 1), hnat (e 2), hnat (e 3)]
    simp only [map_add, map_sub, map_mul, map_one] at hP ⊢
    fin_cases i
    · simp only [if_true]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 0 : K)) * hP
    · simp only [if_false, if_true]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 1 : K)) * hP
    · simp only [if_false, if_true]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 2 : K)) * hP
    · simp only [if_false]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 3 : K)) * hP
  · have hzero := D.stationaryRamifiedFamily_coeff_eq_zero_of_not_carrier_mem he
    rw [hzero]
    simp

/-- **Falling monomial-curve source row.**  This is the Hessian-level form of
`stationaryRamifiedFamily_curveEuler`. -/
theorem stationaryRamifiedFamily_curveEulerRow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (i : Fin 4) :
    MvPolynomial.C (Polynomial.C (F.V : K)) *
        HC4.Polynomial.eulerScaledHessian
          D.stationaryRamifiedFamily i (0 : Fin 4) +
      MvPolynomial.C (Polynomial.C (F.V : K)) *
        HC4.Polynomial.eulerScaledHessian
          D.stationaryRamifiedFamily i (1 : Fin 4) +
      MvPolynomial.C (Polynomial.C (F.V : K)) *
        HC4.Polynomial.eulerScaledHessian
          D.stationaryRamifiedFamily i (2 : Fin 4) -
        HC4.Polynomial.eulerScaledHessian
          D.stationaryRamifiedFamily i (3 : Fin 4) =
    MvPolynomial.C
        (Polynomial.C
          ((F.V : K) -
            (if i = (0 : Fin 4) then (F.V : K)
             else if i = (1 : Fin 4) then (F.V : K)
             else if i = (2 : Fin 4) then (F.V : K)
             else -1))) *
      HC4.Polynomial.mvEuler i D.stationaryRamifiedFamily := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sub,
    MvPolynomial.coeff_C_mul, coeff_eulerScaledHessian, coeff_mvEuler]
  by_cases he : e ∈ P.carrier.support
  · have hs := F.support_curveEuler_scalar hthree houtThree he
    have hP := congrArg Polynomial.C hs
    have hnat (n : ℕ) :
        (n : Polynomial K) = Polynomial.C (n : K) :=
      (map_natCast (Polynomial.C : K →+* Polynomial K) n).symm
    rw [hnat (e 0), hnat (e 1), hnat (e 2), hnat (e 3)]
    simp only [map_add, map_sub, map_mul, map_one, map_neg] at hP ⊢
    fin_cases i
    · simp only [if_true]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 0 : K)) * hP
    · simp only [if_false, if_true]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 1 : K)) * hP
    · simp only [if_false, if_true]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 2 : K)) * hP
    · simp only [if_false]
      linear_combination
        (MvPolynomial.coeff e D.stationaryRamifiedFamily) *
          (Polynomial.C (e 3 : K)) * hP
  · have hzero := D.stationaryRamifiedFamily_coeff_eq_zero_of_not_carrier_mem he
    rw [hzero]
    simp

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
