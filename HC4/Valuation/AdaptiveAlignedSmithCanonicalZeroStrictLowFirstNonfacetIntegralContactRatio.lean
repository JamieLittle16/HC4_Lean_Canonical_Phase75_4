import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetLockedFrontier
import Mathlib.Tactic

/-!
# A19.96: the degree-one lower `qs` contact ratio is integral

The first-nonfacet carrier is deliberately balance-free, so the old balanced
rank-three endpoint obstruction is not an admissible shortcut here.  What the
current carrier does retain is stronger first-contact arithmetic.

A19.75/A19.90 force the actual outside step of the surviving rank-three `qs`
ray to have omitted coordinate exactly one.  Substituting that unit coordinate
into the denominator-cleared first-contact equation gives

    bump = scale * (top degree - outside degree).

Thus the rational first-contact slope is already integral.  In the genuine
other-facet branch A19.88 supplies a two-degree drop, so the integral ratio is
at least two.  These statements use only the exact contact equation retained
by A19.66; no torus-balance hypothesis is reintroduced.  This is the
normalization datum needed by the next source-native contact reduction.
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

/-- The unit omitted-coordinate step turns the cleared first-contact equation
into an exact natural-number degree-gap identity. -/
theorem qs_ray_bump_eq_scale_mul_outsideDegreeGap
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.bump = C.scale *
      (T.topFace.degree - HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent) := by
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hcontact := C.ray_contact_eq
    C.ray.outsideExponent C.ray.outside_mem
  unfold HC4.Newton.scaledContactExponentWeight at hcontact
  rw [hout0] at hcontact
  norm_num at hcontact
  have hcontactNat :
      C.scale * HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent + C.bump =
        C.scale * T.topFace.degree := by
    exact_mod_cast hcontact
  rw [Nat.mul_sub_left_distrib]
  omega

/-- Equivalently, the denominator-cleared first-contact scale divides its
bump: the surviving degree-one `qs` contact has integral rational slope. -/
theorem qs_ray_scale_dvd_bump
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    C.scale ∣ C.bump := by
  refine ⟨T.topFace.degree -
    HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent, ?_⟩
  exact C.qs_ray_bump_eq_scale_mul_outsideDegreeGap hthree

/-- In the genuine different-facet branch the integral first-contact ratio is
at least two, because A19.88 gives an ordinary-degree drop of at least two. -/
theorem qs_ray_otherFacet_two_mul_scale_le_bump
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    2 * C.scale ≤ C.bump := by
  have hgap := C.qs_ray_rankThree_otherFacet_degree_add_two_le_topFace
    hthree hne houtThree
  have htwo :
      2 ≤ T.topFace.degree -
        HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent := by
    omega
  have heq := C.qs_ray_bump_eq_scale_mul_outsideDegreeGap hthree
  calc
    2 * C.scale = C.scale * 2 := by omega
    _ ≤ C.scale *
        (T.topFace.degree -
          HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent) :=
      Nat.mul_le_mul_left C.scale htwo
    _ = C.bump := heq.symm

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
