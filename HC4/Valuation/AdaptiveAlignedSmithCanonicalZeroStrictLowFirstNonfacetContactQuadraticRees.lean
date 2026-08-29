import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactRees
import Mathlib.Tactic

/-!
# A19.112: quadratic clock margin for the integral contact Rees

The final one-variable staircase profile is governed by the original integral
`.qs` contact weight, not by the later lexicographic ray-refinement weight.
For contact gap `r` this natural source weight is literally

    (r+1, 1, 1, 1),

so the binary longitudinal profile weight is `r+1`.

A19.101 only recorded positivity of the contact determinant clock.  The
strict-low source contains an actual monomial of ordinary degree at least three
and longitudinal exponent at least two.  The same contact bound therefore
forces

    2*r + 3 <= D.

Together with `r >= 2`, this gives the stronger quadratic margin

    2*D < 4*D - 2*(r+4).

Hence every quadratic convolution of source layers in the integral contact
Rees occurs strictly before determinant closure.
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

/-- Contact-native Rees package with the exact binary profile weight and enough
clock margin for every quadratic profile coefficient. -/
structure QsOtherFacetContactQuadraticReesPackage
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) where
  contactGap : ℕ
  bound : HasReverseWeightBound
    (qsIntegralContactWeight contactGap) T.topFace.degree
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
  contactGap_two_le : 2 ≤ contactGap
  bump_eq : C.bump = C.scale * contactGap
  source_weight_le :
    ∀ {d : Fin 4 →₀ ℕ},
      d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support →
      HC4.Polynomial.ordinaryDegree4 d +
          contactGap * d (0 : Fin 4) ≤ T.topFace.degree
  profileWeight : ℕ
  profileWeight_eq : profileWeight = contactGap + 1
  profileWeight_two_le : 2 ≤ profileWeight
  specialFiber_eq_contact :
    polynomialFamilySpecialFiber
        (reverseWeightedReesFamily
          (qsIntegralContactWeight contactGap) T.topFace.degree
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) bound) =
      HC4.Polynomial.initialForm
        (HC4.Newton.scaledContactWeight (0 : Fin 4) 1 contactGap)
        (T.topFace.degree : ℤ)
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
  special_hessian_zero :
    HC4.Polynomial.hessianDeterminant
      (polynomialFamilySpecialFiber
        (reverseWeightedReesFamily
          (qsIntegralContactWeight contactGap) T.topFace.degree
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) bound)) = 0
  hessianDefect :
    HasPolynomialFamilyHessianDefect (K := K)
      (reverseWeightedReesFamily
        (qsIntegralContactWeight contactGap) T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) bound)
      (4 * T.topFace.degree - 2 * (contactGap + 4))
  two_level_lt_defect :
    2 * T.topFace.degree <
      4 * T.topFace.degree - 2 * (contactGap + 4)
  positiveLayer :
    HasPositiveActualParameterLayer
      (reverseWeightedReesFamily
        (qsIntegralContactWeight contactGap) T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) bound)

/-- **A19.112 contact quadratic-Rees package.** -/
theorem qs_ray_otherFacet_contactQuadraticRees_package
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    Nonempty (QsOtherFacetContactQuadraticReesPackage C) := by
  rcases C.qs_ray_otherFacet_contactRees_package hthree hne houtThree with
    ⟨r, hbound, hr, hbump, hsource, hspecial, hzero, hdef,
      _hdelta, hpositive⟩
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨d, hd, hdeg, hd0, _hcodim⟩
  have hdBound := hsource hd
  have hstrong : 2 * r + 3 ≤ T.topFace.degree := by
    omega
  have hquadratic :
      2 * T.topFace.degree <
        4 * T.topFace.degree - 2 * (r + 4) := by
    omega
  refine ⟨{
    contactGap := r
    bound := hbound
    contactGap_two_le := hr
    bump_eq := hbump
    source_weight_le := hsource
    profileWeight := r + 1
    profileWeight_eq := rfl
    profileWeight_two_le := by omega
    specialFiber_eq_contact := hspecial
    special_hessian_zero := hzero
    hessianDefect := hdef
    two_level_lt_defect := hquadratic
    positiveLayer := hpositive
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
