import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedCarrier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralSourceContact
import Mathlib.Tactic

/-!
# A19 source contact slope of the normalized PR carrier

The integral lower `.qs` contact is retained on the *actual represented source*:

    ordinaryDegree4 d + r * d₀ = D

for every exponent on the locked ray.  If the locked `.pr` direction is

    (1,-1,-alpha,-beta),

then comparing its two actual endpoints gives the exact identity

    r = alpha + beta.

Consequently the normalized carrier frontier sharpens to:

* unit direction `(1,-1,-1,-1)`  ->  `r = 2`;
* left/right `V>1` direction      ->  `r = V + 1`.

This is the source-honest contact/slope coupling needed by the final carrier
reconstruction.  It does not identify the contact filtration parameter with
the blocker or ray clock; it uses only the retained source contact equality on
the locked ray.
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

/-- Equal integral contact weight on the two literal locked source endpoints
forces the contact gap to equal the sum of the two normalized transverse
drops. -/
theorem QsOtherFacetPrQuotientCarrierData.contactSlope_eq_sum
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta r : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (hray : ∀ {d : Fin 4 →₀ ℕ}, d ∈ C.ray.face.support →
      HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) =
        T.topFace.degree) :
    r = alpha + beta := by
  have h0Z := Q.direction_zero
  have h1Z := Q.direction_one
  have h2Z := Q.direction_two
  have h3Z := Q.direction_three
  have h0 : C.ray.outsideExponent 0 = C.ray.facetExponent 0 + 1 := by
    exact_mod_cast (show
      (C.ray.outsideExponent 0 : ℤ) =
        (C.ray.facetExponent 0 : ℤ) + 1 by omega)
  have h1 : C.ray.facetExponent 1 = C.ray.outsideExponent 1 + 1 := by
    exact_mod_cast (show
      (C.ray.facetExponent 1 : ℤ) =
        (C.ray.outsideExponent 1 : ℤ) + 1 by omega)
  have h2 : C.ray.facetExponent 2 = C.ray.outsideExponent 2 + alpha := by
    exact_mod_cast (show
      (C.ray.facetExponent 2 : ℤ) =
        (C.ray.outsideExponent 2 : ℤ) + (alpha : ℤ) by omega)
  have h3 : C.ray.facetExponent 3 = C.ray.outsideExponent 3 + beta := by
    exact_mod_cast (show
      (C.ray.facetExponent 3 : ℤ) =
        (C.ray.outsideExponent 3 : ℤ) + (beta : ℤ) by omega)
  have hdeg :
      HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent =
        HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent + alpha + beta := by
    simp [HC4.Polynomial.ordinaryDegree4, h0, h1, h2, h3]
    omega
  have hf := hray C.ray.facet_mem_face
  have ho := hray C.ray.outside_mem_face
  rw [hdeg] at hf
  rw [h0] at ho
  simp only [Nat.mul_add, Nat.mul_one] at ho
  omega

/-- Exact integral source contact data in the coordinate form used by the
normalized `.pr` carrier. -/
theorem qs_ray_pr_integral_source_contact
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ r : ℕ,
      2 ≤ r ∧
      C.bump = C.scale * r ∧
      (∀ {d : Fin 4 →₀ ℕ},
        d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support →
        HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) ≤
          T.topFace.degree) ∧
      (∀ {d : Fin 4 →₀ ℕ}, d ∈ C.ray.face.support →
        HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) =
          T.topFace.degree) := by
  rcases C.qs_ray_otherFacet_integral_source_contact
      hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree with
    ⟨r, hr, hbump, hsource, hray⟩
  refine ⟨r, hr, hbump, ?_, ?_⟩
  · intro d hd
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hsource hd
  · intro d hd
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hray hd

/-- **Contact-aware normalized carrier frontier.**  The exact integral source
contact slope is `2` in the unit case and `V+1` in either genuine `V>1`
orientation, while the full source bound and locked-ray contact equality are
retained for the reconstruction step. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_contactSlope_frontier
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ r : ℕ,
      2 ≤ r ∧
      C.bump = C.scale * r ∧
      (∀ {d : Fin 4 →₀ ℕ},
        d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support →
        HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) ≤
          T.topFace.degree) ∧
      (∀ {d : Fin 4 →₀ ℕ}, d ∈ C.ray.face.support →
        HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) =
          T.topFace.degree) ∧
      ((r = 2 ∧
          Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 1)) ∨
        ∃ V : ℕ, 1 < V ∧ r = V + 1 ∧
          (Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 V) ∨
            Nonempty (QsOtherFacetPrQuotientCarrierData C P V 1))) := by
  rcases C.qs_ray_pr_integral_source_contact hthree houtThree with
    ⟨r, hr, hbump, hsource, hray⟩
  refine ⟨r, hr, hbump, hsource, hray, ?_⟩
  rcases S.pr_normalizedCarrier_frontier
      hthree houtThree hnontrivial with hunit | hV
  · rcases hunit with ⟨Q⟩
    have hrsum := Q.contactSlope_eq_sum hray
    left
    exact ⟨by omega, ⟨Q⟩⟩
  · rcases hV with ⟨V, hVgt, horient⟩
    right
    refine ⟨V, hVgt, ?_, horient⟩
    rcases horient with hleft | hright
    · rcases hleft with ⟨Q⟩
      have hrsum := Q.contactSlope_eq_sum hray
      omega
    · rcases hright with ⟨Q⟩
      have hrsum := Q.contactSlope_eq_sum hray
      omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
