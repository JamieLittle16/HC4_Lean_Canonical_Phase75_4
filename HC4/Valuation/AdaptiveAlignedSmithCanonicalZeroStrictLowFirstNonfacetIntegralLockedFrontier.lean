import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralSourceContact
import Mathlib.Tactic

/-!
# A19.98: integral locked lower `qs` other-facet frontier

A19.95 packages the surviving different-facet endpoint as one of the three
explicit strict transverse direction locks.  A19.97 independently normalizes
the same first-contact carrier to an honest integral source weight of slope
`r >= 2`, with the weight bounded on the represented source and equal to the
old top degree on the extracted affine ray.

This file is the assembly seam between those two facts.  It deliberately adds
no new descent measure, carrier, balance hypothesis, or planar reduction: the
same `CrossFacetData` witness is retained, now carrying both the integral
source contact and the finite-support direction lock needed by the existing
binary staircase/profile rigidity layer.
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

-- CI anchor: elaborate A19.98 after the generated inventory refresh.

/-- **A19.98 integral locked source-contact interface.**  A genuine lower
`.qs` ray whose actual outside endpoint lies rank three on a different facet
has a single integral slope `r >= 2` governing the represented-source contact,
while the two positive transverse coordinates undergo the already-proved
strict same-ray drop in the appropriate cyclic pair. -/
theorem qs_ray_otherFacet_integral_locked_source_contact
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
          T.topFace.degree) ∧
      ((HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent ∧
          C.ray.facetExponent 2 * C.ray.outsideExponent 3 =
            C.ray.facetExponent 3 * C.ray.outsideExponent 2 ∧
          C.ray.outsideExponent 2 < C.ray.facetExponent 2 ∧
          C.ray.outsideExponent 3 < C.ray.facetExponent 3) ∨
        (HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent ∧
          C.ray.facetExponent 1 * C.ray.outsideExponent 3 =
            C.ray.facetExponent 3 * C.ray.outsideExponent 1 ∧
          C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
          C.ray.outsideExponent 3 < C.ray.facetExponent 3) ∨
        (HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent ∧
          C.ray.facetExponent 1 * C.ray.outsideExponent 2 =
            C.ray.facetExponent 2 * C.ray.outsideExponent 1 ∧
          C.ray.outsideExponent 1 < C.ray.facetExponent 1 ∧
          C.ray.outsideExponent 2 < C.ray.facetExponent 2)) := by
  rcases C.qs_ray_otherFacet_integral_source_contact hthree hne houtThree with
    ⟨r, hr, hbump, hsource, hray⟩
  refine ⟨r, hr, hbump, hsource, hray, ?_⟩
  exact C.qs_ray_otherFacet_strict_directionLock hthree hne houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
