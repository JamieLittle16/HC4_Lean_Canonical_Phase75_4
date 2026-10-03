import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryLongitudinalHessianCoefficients
import Mathlib.Tactic

/-!
# A19 source-honest Euler equations of the left non-unit planar carrier

The final Schur/profile adapter needs the two affine equations defining the
actual planar carrier as whole-polynomial identities, not only as support
arithmetic.  The quotient staircase already proves, for every source monomial,

    (n-1)(r-1) = ell(n-k),
    s = V(k+r-1),

with

    k = e0+e1,  r = e0+e2,  s = V*e0+e3.

This file clears those equations into the corresponding Euler identities of
the literal source carrier.  No division, localization, reconstructed support,
or auxiliary clock is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVContactFrontierData

/-- The staircase wall equation in source coordinates, cast to the ground
field. -/
theorem support_wallEuler_scalar
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    ((((F.highest.n : K) - 1) + (F.locked.ell : K)) * (e 0 : K) +
        (F.locked.ell : K) * (e 1 : K) +
        ((F.highest.n : K) - 1) * (e 2 : K)) =
      ((F.highest.n : K) - 1) +
        (F.locked.ell : K) * (F.highest.n : K) := by
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp [HC4.Polynomial.rankThreeQuotientCoordinate] at hs
  have hz :
      (((F.highest.n : ℤ) - 1) * ((e 0 : ℤ) + (e 2 : ℤ)) +
          (F.locked.ell : ℤ) * ((e 0 : ℤ) + (e 1 : ℤ))) =
        ((F.highest.n : ℤ) - 1) +
          (F.locked.ell : ℤ) * (F.highest.n : ℤ) := by
    nlinarith [hs.1]
  have hk :
      (((F.highest.n : K) - 1) * ((e 0 : K) + (e 2 : K)) +
          (F.locked.ell : K) * ((e 0 : K) + (e 1 : K))) =
        ((F.highest.n : K) - 1) +
          (F.locked.ell : K) * (F.highest.n : K) := by
    exact_mod_cast hz
  calc
    (((F.highest.n : K) - 1) + (F.locked.ell : K)) * (e 0 : K) +
          (F.locked.ell : K) * (e 1 : K) +
          ((F.highest.n : K) - 1) * (e 2 : K) =
        ((F.highest.n : K) - 1) * ((e 0 : K) + (e 2 : K)) +
          (F.locked.ell : K) * ((e 0 : K) + (e 1 : K)) := by ring
    _ = ((F.highest.n : K) - 1) +
          (F.locked.ell : K) * (F.highest.n : K) := hk

/-- The monomial-curve equation in source coordinates, cast to the ground
field. -/
theorem support_curveEuler_scalar
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    (F.V : K) * (e 0 : K) +
        (F.V : K) * (e 1 : K) +
        (F.V : K) * (e 2 : K) =
      (F.V : K) + (e 3 : K) := by
  have hs := F.support_staircase_equations hthree houtThree he
  dsimp [HC4.Polynomial.rankThreeQuotientCoordinate] at hs
  have hz :
      (F.V : ℤ) * (e 0 : ℤ) +
          (F.V : ℤ) * (e 1 : ℤ) +
          (F.V : ℤ) * (e 2 : ℤ) =
        (F.V : ℤ) + (e 3 : ℤ) := by
    nlinarith [hs.2]
  exact_mod_cast hz

/-- **First planar Euler equation.**  The staircase wall is an exact weighted
homogeneity equation of the literal source carrier. -/
theorem carrier_wallEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    MvPolynomial.C
        (((F.highest.n : K) - 1) + (F.locked.ell : K)) *
          HC4.Polynomial.mvEuler (0 : Fin 4) P.carrier +
      MvPolynomial.C (F.locked.ell : K) *
          HC4.Polynomial.mvEuler (1 : Fin 4) P.carrier +
      MvPolynomial.C ((F.highest.n : K) - 1) *
          HC4.Polynomial.mvEuler (2 : Fin 4) P.carrier =
    MvPolynomial.C
        (((F.highest.n : K) - 1) +
          (F.locked.ell : K) * (F.highest.n : K)) * P.carrier := by
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, coeff_mvEuler]
  by_cases hc : MvPolynomial.coeff e P.carrier = 0
  · simp [hc]
  · have he : e ∈ P.carrier.support := MvPolynomial.mem_support_iff.mpr hc
    have hs := F.support_wallEuler_scalar hthree houtThree he
    linear_combination (MvPolynomial.coeff e P.carrier) * hs

/-- **Second planar Euler equation.**  The source monomial-curve relation is
an exact affine Euler equation of the literal carrier. -/
theorem carrier_curveEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    MvPolynomial.C (F.V : K) * HC4.Polynomial.mvEuler (0 : Fin 4) P.carrier +
        MvPolynomial.C (F.V : K) * HC4.Polynomial.mvEuler (1 : Fin 4) P.carrier +
        MvPolynomial.C (F.V : K) * HC4.Polynomial.mvEuler (2 : Fin 4) P.carrier =
      MvPolynomial.C (F.V : K) * P.carrier +
        HC4.Polynomial.mvEuler (3 : Fin 4) P.carrier := by
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, coeff_mvEuler]
  by_cases hc : MvPolynomial.coeff e P.carrier = 0
  · simp [hc]
  · have he : e ∈ P.carrier.support := MvPolynomial.mem_support_iff.mpr hc
    have hs := F.support_curveEuler_scalar hthree houtThree he
    linear_combination (MvPolynomial.coeff e P.carrier) * hs

end QsOtherFacetPrLeftVContactFrontierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation