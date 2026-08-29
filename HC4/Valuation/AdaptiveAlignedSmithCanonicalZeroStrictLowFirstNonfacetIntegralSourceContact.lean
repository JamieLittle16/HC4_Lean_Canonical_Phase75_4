import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralContactRatio
import Mathlib.Tactic

/-!
# A19.97: normalize the lower `qs` contact to an integral source weight

A19.96 proves that the denominator-cleared first-contact bump is divisible by
its scale.  In the genuine other-facet branch the quotient is at least two.
This file performs only the corresponding cancellation on the already-retained
source contact inequality and ray contact equality.

Thus the rational first-contact weight is replaced by the honest integral
weight

    ordinaryDegree4 d + r * d[omitted]

with `2 ≤ r`, bounded by the old maximal top degree on every represented-source
monomial and equal to it on every monomial of the extracted affine ray.

No new carrier, progress measure, balance hypothesis, or planar reduction is
introduced.  This is the source-native normalization promised by A19.96.
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

/-- In the surviving different-facet lower `.qs` branch, the cleared rational
contact is already an honest integral source weight of slope at least two. -/
theorem qs_ray_otherFacet_integral_source_contact
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    ∃ r : ℕ,
      2 ≤ r ∧
      C.bump = C.scale * r ∧
      (∀ {d : Fin 4 →₀ ℕ},
        d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support →
        HC4.Polynomial.ordinaryDegree4 d +
            r * d (HC4.Polynomial.facetOmittedCoordinate .qs) ≤
          T.topFace.degree) ∧
      (∀ {d : Fin 4 →₀ ℕ}, d ∈ C.ray.face.support →
        HC4.Polynomial.ordinaryDegree4 d +
            r * d (HC4.Polynomial.facetOmittedCoordinate .qs) =
          T.topFace.degree) := by
  rcases C.qs_ray_scale_dvd_bump hthree with ⟨r, hr⟩
  have htwoScale :=
    C.qs_ray_otherFacet_two_mul_scale_le_bump hthree hne houtThree
  have hrTwo : 2 ≤ r := by
    rw [hr] at htwoScale
    by_contra hnot
    have hlt : r < 2 := Nat.lt_of_not_ge hnot
    have hmul : C.scale * r < C.scale * 2 :=
      Nat.mul_lt_mul_of_pos_left hlt C.scale_pos
    omega
  refine ⟨r, hrTwo, hr, ?_, ?_⟩
  · intro d hd
    have hcontact := C.source_contact_le hd
    unfold HC4.Newton.scaledContactExponentWeight at hcontact
    rw [hr] at hcontact
    have hnat :
        C.scale * HC4.Polynomial.ordinaryDegree4 d +
            (C.scale * r) * d (HC4.Polynomial.facetOmittedCoordinate .qs) ≤
          C.scale * T.topFace.degree := by
      exact_mod_cast hcontact
    have hfactored :
        C.scale *
            (HC4.Polynomial.ordinaryDegree4 d +
              r * d (HC4.Polynomial.facetOmittedCoordinate .qs)) ≤
          C.scale * T.topFace.degree := by
      simpa [Nat.mul_add, Nat.mul_assoc] using hnat
    by_contra hnot
    have hlt :
        T.topFace.degree <
          HC4.Polynomial.ordinaryDegree4 d +
            r * d (HC4.Polynomial.facetOmittedCoordinate .qs) :=
      Nat.lt_of_not_ge hnot
    have hmul := Nat.mul_lt_mul_of_pos_left hlt C.scale_pos
    omega
  · intro d hd
    have hcontact := C.ray_contact_eq d hd
    unfold HC4.Newton.scaledContactExponentWeight at hcontact
    rw [hr] at hcontact
    have hnat :
        C.scale * HC4.Polynomial.ordinaryDegree4 d +
            (C.scale * r) * d (HC4.Polynomial.facetOmittedCoordinate .qs) =
          C.scale * T.topFace.degree := by
      exact_mod_cast hcontact
    have hfactored :
        C.scale *
            (HC4.Polynomial.ordinaryDegree4 d +
              r * d (HC4.Polynomial.facetOmittedCoordinate .qs)) =
          C.scale * T.topFace.degree := by
      simpa [Nat.mul_add, Nat.mul_assoc] using hnat
    by_contra hneDegree
    rcases Nat.lt_or_gt_of_ne hneDegree with hlt | hgt
    · have hmul := Nat.mul_lt_mul_of_pos_left hlt C.scale_pos
      omega
    · have hmul := Nat.mul_lt_mul_of_pos_left hgt C.scale_pos
      omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
