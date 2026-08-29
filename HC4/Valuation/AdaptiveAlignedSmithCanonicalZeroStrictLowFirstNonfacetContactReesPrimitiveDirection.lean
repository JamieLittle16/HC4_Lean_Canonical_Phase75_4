import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetWeightedContactPrimitiveDirection
import Mathlib.Tactic

/-!
# A19.102: primitive direction at the chosen contact-Rees slope

A19.101 chooses the unique integral slope `r` used by the honest reverse Rees
family.  A19.100d previously produced an existential slope from the same
cleared contact.  Positivity of the retained scale makes those slopes equal.
This file exposes the primitive direction directly at the A19.101 slope, so
later straightening never has to reconcile two existential parameters.
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

/-- Two integral slopes representing the same positive-scale cleared bump are
equal. -/
theorem contactSlope_eq_of_bump_eq
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    {r s : ℕ}
    (hr : C.bump = C.scale * r)
    (hs : C.bump = C.scale * s) :
    r = s := by
  apply Nat.mul_left_cancel C.scale_pos
  rw [← hr, ← hs]

/-- `.pr`: primitive direction using a caller-supplied integral contact slope. -/
theorem qs_ray_pr_primitiveDirection_of_bump_eq
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (r : ℕ)
    (hr : 2 ≤ r)
    (hbump : C.bump = C.scale * r) :
    ∃ a b h k : ℕ,
      0 < a ∧ 0 < b ∧ 0 < h ∧ 0 < k ∧ Nat.Coprime a b ∧
      C.ray.facetExponent 2 = (h + k) * a ∧
      C.ray.facetExponent 3 = (h + k) * b ∧
      C.ray.outsideExponent 2 = h * a ∧
      C.ray.outsideExponent 3 = h * b ∧
      r = k * (a + b) ∧ 2 ≤ a + b := by
  rcases C.qs_ray_pr_integral_contactGap_primitiveDirection
      hthree houtThree with
    ⟨s, a, b, h, k, hsTwo, ha, hb, hh, hk, hab, hsBump,
      h2, h3, ho2, ho3, hsEq, habTwo⟩
  have hrs : r = s := C.contactSlope_eq_of_bump_eq hbump hsBump
  subst s
  exact ⟨a, b, h, k, ha, hb, hh, hk, hab,
    h2, h3, ho2, ho3, hsEq, habTwo⟩

/-- `.sp`: primitive direction using the same chosen contact-Rees slope. -/
theorem qs_ray_sp_primitiveDirection_of_bump_eq
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent)
    (r : ℕ)
    (hr : 2 ≤ r)
    (hbump : C.bump = C.scale * r) :
    ∃ a b h k : ℕ,
      0 < a ∧ 0 < b ∧ 0 < h ∧ 0 < k ∧ Nat.Coprime a b ∧
      C.ray.facetExponent 1 = (h + k) * a ∧
      C.ray.facetExponent 3 = (h + k) * b ∧
      C.ray.outsideExponent 1 = h * a ∧
      C.ray.outsideExponent 3 = h * b ∧
      r = k * (a + b) ∧ 2 ≤ a + b := by
  rcases C.qs_ray_sp_integral_contactGap_primitiveDirection
      hthree houtThree with
    ⟨s, a, b, h, k, hsTwo, ha, hb, hh, hk, hab, hsBump,
      h1, h3, ho1, ho3, hsEq, habTwo⟩
  have hrs : r = s := C.contactSlope_eq_of_bump_eq hbump hsBump
  subst s
  exact ⟨a, b, h, k, ha, hb, hh, hk, hab,
    h1, h3, ho1, ho3, hsEq, habTwo⟩

/-- `.rq`: primitive direction using the same chosen contact-Rees slope. -/
theorem qs_ray_rq_primitiveDirection_of_bump_eq
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent)
    (r : ℕ)
    (hr : 2 ≤ r)
    (hbump : C.bump = C.scale * r) :
    ∃ a b h k : ℕ,
      0 < a ∧ 0 < b ∧ 0 < h ∧ 0 < k ∧ Nat.Coprime a b ∧
      C.ray.facetExponent 1 = (h + k) * a ∧
      C.ray.facetExponent 2 = (h + k) * b ∧
      C.ray.outsideExponent 1 = h * a ∧
      C.ray.outsideExponent 2 = h * b ∧
      r = k * (a + b) ∧ 2 ≤ a + b := by
  rcases C.qs_ray_rq_integral_contactGap_primitiveDirection
      hthree houtThree with
    ⟨s, a, b, h, k, hsTwo, ha, hb, hh, hk, hab, hsBump,
      h1, h2, ho1, ho2, hsEq, habTwo⟩
  have hrs : r = s := C.contactSlope_eq_of_bump_eq hbump hsBump
  subst s
  exact ⟨a, b, h, k, ha, hb, hh, hk, hab,
    h1, h2, ho1, ho2, hsEq, habTwo⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
