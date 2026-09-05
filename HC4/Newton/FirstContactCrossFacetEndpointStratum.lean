import HC4.Newton.FirstContactCrossFacetAffineLine
import HC4.Newton.MvBoundaryStrata
import Mathlib.Tactic

/-!
# A18.5.66: endpoint stratum of the honest cross-facet line

A18.5.65d proves that the exact secondary face crossing the first-contact
facet is genuinely one-dimensional.  The remaining geometric datum needed by
the RationalRigidity endgame is the stratum of its certified facet endpoint.

There is no need to forget which facet was used.  The contact coordinate `j`
already determines the toric facet whose omitted coordinate is `j`.  The
certified facet exponent lies on that facet literally, so the existing toric
classification `rankThree_or_transitionRay_of_onFacet` applies directly.
Thus the endpoint is either

* rank three in the relative interior of the *same* contact facet; or
* on an extreme transition ray from that facet to one of its two neighbours.

The final theorem packages this endpoint split together with all of the honest
line data already needed downstream: both actual endpoint coefficients are
nonzero, zero Hessian determinant passes to the exact face, and every support
exponent satisfies the affine-line proportionality from A18.5.65d.

In the canonical `qs` chart, whose omitted coordinate is `0`, the rank-three
alternative is exactly positivity of coordinates `1,2,3`.  This is the chart
used by the mature affine rank-three RationalRigidity realization.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The toric facet whose omitted coordinate is the chosen contact coordinate.
This is the inverse of `facetOmittedCoordinate`. -/
def crossFacetContactFacet (j : Fin 4) : ToricFacet :=
  ![.qs, .pr, .sp, .rq] j

@[simp] theorem facetOmittedCoordinate_crossFacetContactFacet
    (j : Fin 4) :
    facetOmittedCoordinate (crossFacetContactFacet j) = j := by
  fin_cases j <;> rfl

@[simp] theorem crossFacetContactFacet_facetOmittedCoordinate
    (F : ToricFacet) :
    crossFacetContactFacet (facetOmittedCoordinate F) = F := by
  cases F <;> rfl

/-- The certified facet endpoint of a cross-facet initial form lies on the
contact facet selected by its zero coordinate. -/
theorem CrossFacetInitialData.facetExponent_on_contactFacet
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j) :
    OnFacet (crossFacetContactFacet j) (toToricExponent D.facetExponent) := by
  rw [onFacet_toToricExponent_iff]
  simpa using D.facet_coordinate_zero

/-- **Endpoint classification on the actual contact facet.**

A balanced facet endpoint is either rank three in the relative interior of
that very facet, or lies on one of its two extreme transition rays.  Unlike a
generic boundary classification, the ray branch retains the original contact
facet as the first endpoint of `AdjacentFacets`. -/
theorem CrossFacetInitialData.facetEndpoint_rankThree_or_transitionRay
    {F : MvPolynomial (Fin 4) K}
    {a b : ℕ} {i j : Fin 4}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (D : CrossFacetInitialData F i j)
    (hBal : HasBalancedMvSupport a b F) :
    MvRankThreeOnFacet (crossFacetContactFacet j) D.facetExponent ∨
      ∃ G : ToricFacet,
        AdjacentFacets (crossFacetContactFacet j) G ∧
          OnRay a b (crossFacetContactFacet j) G
            (toToricExponent D.facetExponent) := by
  have hBalMv : IsBalancedExponent a b D.facetExponent :=
    hBal D.facetExponent D.facet_mem
  have hBalToric : Balanced a b (toToricExponent D.facetExponent) :=
    (isBalancedExponent_iff_balanced a b D.facetExponent).1 hBalMv
  rcases rankThree_or_transitionRay_of_onFacet
      ha hb hcop hBalToric D.facetExponent_on_contactFacet with
    hthree | hray
  · exact Or.inl hthree
  · exact Or.inr hray

/-- Complete support-level certificate carried by the honest cross-facet line.
The first three fields are literal polynomial data; the final field is the
rank-one affine support relation proved in A18.5.65d. -/
def CrossFacetHonestLineCertificate
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {j : Fin 4}
    (D : CrossFacetInitialData F (crossFacetOppositeCoordinate j) j)
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight j contactScale contactBump d = contactLevel) :
    Prop :=
  MvPolynomial.coeff D.facetExponent D.face ≠ 0 ∧
  MvPolynomial.coeff D.outsideExponent D.face ≠ 0 ∧
  hessianDeterminant D.face = 0 ∧
  ∀ d ∈ D.face.support, ∀ k : Fin 4,
    (((D.outsideExponent j : ℕ) : ℤ) -
        ((D.facetExponent j : ℕ) : ℤ)) *
        (((d k : ℕ) : ℤ) - ((D.facetExponent k : ℕ) : ℤ)) =
      (((d j : ℕ) : ℤ) - ((D.facetExponent j : ℕ) : ℤ)) *
        (((D.outsideExponent k : ℕ) : ℤ) -
          ((D.facetExponent k : ℕ) : ℤ))

/-- The exact cross-facet face carries the complete honest-line certificate
whenever the original carrier is Hessian-singular. -/
theorem CrossFacetInitialData.honestLineCertificate
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {j : Fin 4}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F (crossFacetOppositeCoordinate j) j)
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight j contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0) :
    CrossFacetHonestLineCertificate D hBal hcontact := by
  refine ⟨MvPolynomial.mem_support_iff.mp D.facet_mem_face,
    MvPolynomial.mem_support_iff.mp D.outside_mem_face,
    D.hessian_zero hzero, ?_⟩
  exact D.support_crossFacet_affine_proportional
    ha hb hcontactScale hBal hcontact

/-- **A18.5.66 cross-facet endpoint certificate.**

The honest one-dimensional face and its toric endpoint classification are
available simultaneously.  The rank-three branch is already on the exact
contact facet; the complementary branch is already expressed by the existing
`AdjacentFacets`/`OnRay` interface. -/
theorem CrossFacetInitialData.honestLine_rankThree_or_transitionRay
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    {j : Fin 4}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F (crossFacetOppositeCoordinate j) j)
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight j contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0) :
    CrossFacetHonestLineCertificate D hBal hcontact ∧
      (MvRankThreeOnFacet (crossFacetContactFacet j) D.facetExponent ∨
        ∃ G : ToricFacet,
          AdjacentFacets (crossFacetContactFacet j) G ∧
            OnRay a b (crossFacetContactFacet j) G
              (toToricExponent D.facetExponent)) := by
  constructor
  · exact D.honestLineCertificate ha hb hcontactScale hBal hcontact hzero
  · exact D.facetEndpoint_rankThree_or_transitionRay ha hb hcop hBal

/-- Canonical-coordinate form of the A18.5.66 endpoint split.  In the `qs`
chart the mature affine rank-three RR stack can consume the left branch
directly, while the right branch is an extreme transition ray adjacent to
`qs`. -/
theorem CrossFacetInitialData.honestLine_qs_rankThree_or_transitionRay
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0) :
    CrossFacetHonestLineCertificate D hBal hcontact ∧
      (MvRankThreeOnFacet .qs D.facetExponent ∨
        ∃ G : ToricFacet,
          AdjacentFacets .qs G ∧
            OnRay a b .qs G (toToricExponent D.facetExponent)) := by
  simpa [crossFacetContactFacet] using
    D.honestLine_rankThree_or_transitionRay
      ha hb hcop hcontactScale hBal hcontact hzero

/-- In the canonical rank-three branch, the endpoint has exactly the positive
three-coordinate shape required by the affine RR base exponent. -/
theorem CrossFacetInitialData.qs_rankThree_endpoint_coordinates
    {F : MvPolynomial (Fin 4) K}
    {i : Fin 4}
    (D : CrossFacetInitialData F i (0 : Fin 4))
    (hthree : MvRankThreeOnFacet .qs D.facetExponent) :
    D.facetExponent 0 = 0 ∧
      0 < D.facetExponent 1 ∧
      0 < D.facetExponent 2 ∧
      0 < D.facetExponent 3 := by
  exact mvRankThreeOnFacet_qs hthree

end

end HC4.Newton
