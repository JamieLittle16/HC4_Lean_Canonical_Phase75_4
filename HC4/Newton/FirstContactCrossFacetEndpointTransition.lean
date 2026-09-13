import HC4.Newton.FirstContactCrossFacetEndpointStratum
import HC4.Newton.FirstContactCrossFacetAffineRRTransition
import HC4.Newton.FirstContactCrossFacetAffineRRImpossible
import Mathlib.Tactic

/-!
# A18.5.69: canonical first-contact endpoint transition

A18.5.66 classifies the selected endpoint of the exact honest cross-facet line:
it is either already on an extreme transition ray adjacent to the contact
facet, or it is rank three on that facet.  A18.5.68c identifies the unique
possible affine direction in the latter branch, and A18.5.73b now eliminates
that affine terminal directly.

Thus a genuine positive-bump first contact in the canonical `qs` chart exits
on an actual adjacent extreme ray.  The older two-way dispatcher is retained
below as a compatibility theorem, but downstream final assembly can use the
strong extreme-ray-only endpoint.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **A18.5.69 canonical endpoint dispatcher.**

For a genuine positive-bump first-contact carrier in the canonical `qs` chart,
the exact cross-facet line has its full support certificate and has an actual
geometric exit: either its selected endpoint is already on an extreme ray out
of `qs`, or its far endpoint is rank three on the adjacent `pr` facet.

The second alternative uses exactly the far exponent of the affine RR
realisation; no surrogate support point is introduced. -/
theorem CrossFacetInitialData.qs_firstContact_endpoint_transition
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0) :
    CrossFacetHonestLineCertificate D hBal hcontact ∧
      ((∃ G : ToricFacet,
          AdjacentFacets .qs G ∧
            OnRay a b .qs G (toToricExponent D.facetExponent)) ∨
        MvRankThreeOnFacet .pr
          ((D.qsAffineLineData ha hb hcontactScale hBal hcontact).exponent
            D.qsCoefficientPolynomial.natDegree)) := by
  rcases D.honestLine_qs_rankThree_or_transitionRay
      ha hb hcop hcontactScale hBal hcontact hzero with
    ⟨hcert, hthree | hray⟩
  · refine ⟨hcert, Or.inr ?_⟩
    have htransition := D.qs_rankThree_terminal_transition_pr
      ha hb hcontactScale hcontactBump hBal hcontact hzero hthree
    simpa using htransition.2.2
  · exact ⟨hcert, Or.inl hray⟩

/-- **A18.5.73c: genuine first contact exits on an extreme ray.**

The rank-three endpoint branch of the previous dispatcher is not merely a
transition: its exact affine carrier is impossible.  Therefore the selected
endpoint of every genuine positive-bump `qs` first contact lies on one of the
two adjacent toric extreme rays. -/
theorem CrossFacetInitialData.qs_firstContact_endpoint_extremeRay
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0) :
    CrossFacetHonestLineCertificate D hBal hcontact ∧
      ∃ G : ToricFacet,
        AdjacentFacets .qs G ∧
          OnRay a b .qs G (toToricExponent D.facetExponent) := by
  rcases D.honestLine_qs_rankThree_or_transitionRay
      ha hb hcop hcontactScale hBal hcontact hzero with
    ⟨hcert, hthree | hray⟩
  · exact False.elim
      (D.qs_rankThree_firstContact_impossible
        ha hb hcontactScale hcontactBump hBal hcontact hzero hthree)
  · exact ⟨hcert, hray⟩

end

end HC4.Newton
