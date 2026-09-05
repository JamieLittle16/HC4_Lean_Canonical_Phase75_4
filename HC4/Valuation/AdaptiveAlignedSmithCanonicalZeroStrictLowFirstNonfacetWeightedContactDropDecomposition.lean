import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetWeightedContactDropArithmetic
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetDirectionLock
import Mathlib.Tactic

/-!
# A19.100c: positive locked contact-drop decomposition

The integral weighted contact gap from A19.100b is the total fall in the two
positive transverse coordinates at a surviving different-facet endpoint.
A19.94 separately proves that both coordinates fall strictly while remaining
on the same rational direction.

This file packages those two facts in subtraction-free natural-number form.
For each cyclic other-facet branch there are positive drops `p,q` with

    outside_i + p = facet_i,
    outside_j + q = facet_j,
    contactGap = p + q.

The original cross-product lock is retained verbatim.  This is the exact
primitive-safe arithmetic interface needed by the source-to-binary weighted
profile straightening: no coprimality or primitive-ray hypothesis is assumed.
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

/-- `.pr` branch: expose the two positive locked coordinate drops whose sum is
exactly the integral contact gap. -/
theorem qs_ray_pr_integral_contactGap_positiveDropDecomposition
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ r p q : ℕ,
      2 ≤ r ∧
      0 < p ∧
      0 < q ∧
      C.bump = C.scale * r ∧
      C.ray.outsideExponent 2 + p = C.ray.facetExponent 2 ∧
      C.ray.outsideExponent 3 + q = C.ray.facetExponent 3 ∧
      r = p + q ∧
      C.ray.facetExponent 2 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 2 := by
  rcases C.qs_ray_pr_integral_contactGap_add_outside_eq_facet
      hthree houtThree with ⟨r, hr, hbump, hgap⟩
  rcases C.qs_ray_pr_outside_strict_directionLock hthree houtThree with
    ⟨hcross, hdrop2, hdrop3⟩
  let p := C.ray.facetExponent 2 - C.ray.outsideExponent 2
  let q := C.ray.facetExponent 3 - C.ray.outsideExponent 3
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hpEq : C.ray.outsideExponent 2 + p = C.ray.facetExponent 2 := by
    dsimp [p]
    omega
  have hqEq : C.ray.outsideExponent 3 + q = C.ray.facetExponent 3 := by
    dsimp [q]
    omega
  have hrEq : r = p + q := by
    omega
  exact ⟨r, p, q, hr, hp, hq, hbump, hpEq, hqEq, hrEq, hcross⟩

/-- `.sp` branch: expose the positive locked drops in coordinates `(1,3)`. -/
theorem qs_ray_sp_integral_contactGap_positiveDropDecomposition
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    ∃ r p q : ℕ,
      2 ≤ r ∧
      0 < p ∧
      0 < q ∧
      C.bump = C.scale * r ∧
      C.ray.outsideExponent 1 + p = C.ray.facetExponent 1 ∧
      C.ray.outsideExponent 3 + q = C.ray.facetExponent 3 ∧
      r = p + q ∧
      C.ray.facetExponent 1 * C.ray.outsideExponent 3 =
        C.ray.facetExponent 3 * C.ray.outsideExponent 1 := by
  rcases C.qs_ray_sp_integral_contactGap_add_outside_eq_facet
      hthree houtThree with ⟨r, hr, hbump, hgap⟩
  rcases C.qs_ray_sp_outside_strict_directionLock hthree houtThree with
    ⟨hcross, hdrop1, hdrop3⟩
  let p := C.ray.facetExponent 1 - C.ray.outsideExponent 1
  let q := C.ray.facetExponent 3 - C.ray.outsideExponent 3
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hpEq : C.ray.outsideExponent 1 + p = C.ray.facetExponent 1 := by
    dsimp [p]
    omega
  have hqEq : C.ray.outsideExponent 3 + q = C.ray.facetExponent 3 := by
    dsimp [q]
    omega
  have hrEq : r = p + q := by
    omega
  exact ⟨r, p, q, hr, hp, hq, hbump, hpEq, hqEq, hrEq, hcross⟩

/-- `.rq` branch: expose the positive locked drops in coordinates `(1,2)`. -/
theorem qs_ray_rq_integral_contactGap_positiveDropDecomposition
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    ∃ r p q : ℕ,
      2 ≤ r ∧
      0 < p ∧
      0 < q ∧
      C.bump = C.scale * r ∧
      C.ray.outsideExponent 1 + p = C.ray.facetExponent 1 ∧
      C.ray.outsideExponent 2 + q = C.ray.facetExponent 2 ∧
      r = p + q ∧
      C.ray.facetExponent 1 * C.ray.outsideExponent 2 =
        C.ray.facetExponent 2 * C.ray.outsideExponent 1 := by
  rcases C.qs_ray_rq_integral_contactGap_add_outside_eq_facet
      hthree houtThree with ⟨r, hr, hbump, hgap⟩
  rcases C.qs_ray_rq_outside_strict_directionLock hthree houtThree with
    ⟨hcross, hdrop1, hdrop2⟩
  let p := C.ray.facetExponent 1 - C.ray.outsideExponent 1
  let q := C.ray.facetExponent 2 - C.ray.outsideExponent 2
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hpEq : C.ray.outsideExponent 1 + p = C.ray.facetExponent 1 := by
    dsimp [p]
    omega
  have hqEq : C.ray.outsideExponent 2 + q = C.ray.facetExponent 2 := by
    dsimp [q]
    omega
  have hrEq : r = p + q := by
    omega
  exact ⟨r, p, q, hr, hp, hq, hbump, hpEq, hqEq, hrEq, hcross⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
