import HC4.Newton.FirstContactCrossFacetAffineRRTransition
import HC4.Newton.FirstContactCrossFacetAffineRRReconstruction
import HC4.RationalRigidity.RankThreeAffineTwoFixedImpossible
import Mathlib.Tactic

/-!
# A18.5.73b: the surviving rank-three first-contact branch is impossible

A18.5.68c proves that a genuine positive-bump `qs` first contact can only
survive the finite affine split by fixing transverse coordinates `2` and `3`.
The remaining affine slope cannot be zero: then every transverse coordinate
would be fixed and ordinary degree would increase along the positive omitted
coordinate.  It also cannot be `-1`: then ordinary degree would be preserved.
Both contradict the strict degree drop forced by the positive first-contact
bump.

The affine two-fixed contradiction of A18.5.73a then applies directly to the
exact `RankThreeAffineLineData`.  No integral reparameterisation and no
endpoint divisibility hypothesis is used.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- If the last two affine slopes are fixed, the remaining slope cannot also
vanish: the positive omitted-coordinate motion would strictly increase
ordinary degree, contradicting genuine first-contact descent. -/
private theorem qs_remainingSlope_ne_zero_of_two_fixed
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hR : D.qsSlope (2 : Fin 4) = 0)
    (hS : D.qsSlope (3 : Fin 4) = 0) :
    D.qsSlope (1 : Fin 4) ≠ 0 := by
  have hdegLt := D.qs_outside_ordinaryDegree_lt_facet
    hcontactScale hcontactBump hcontact
  intro hQzero
  have h1fix := D.qs_support_coordinate_eq_facet_of_slope_zero
    ha hb hcontactScale hBal hcontact hQzero D.outside_mem_face
  have h2fix := D.qs_support_coordinate_eq_facet_of_slope_zero
    ha hb hcontactScale hBal hcontact hR D.outside_mem_face
  have h3fix := D.qs_support_coordinate_eq_facet_of_slope_zero
    ha hb hcontactScale hBal hcontact hS D.outside_mem_face
  have hout0 : 0 < D.outsideExponent (0 : Fin 4) :=
    D.outside_coordinate_pos
  have hdegGt : ordinaryDegree4 D.facetExponent <
      ordinaryDegree4 D.outsideExponent := by
    unfold ordinaryDegree4
    rw [D.facet_coordinate_zero, h1fix, h2fix, h3fix]
    omega
  omega

/-- With the last two slopes fixed, the remaining slope cannot be `-1`:
that would preserve ordinary degree, again contradicting the strict
first-contact degree drop. -/
private theorem qs_remainingSlope_add_one_ne_zero_of_two_fixed
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hR : D.qsSlope (2 : Fin 4) = 0)
    (hS : D.qsSlope (3 : Fin 4) = 0) :
    D.qsSlope (1 : Fin 4) + 1 ≠ 0 := by
  have hdegLt := D.qs_outside_ordinaryDegree_lt_facet
    hcontactScale hcontactBump hcontact
  intro hQoneZero
  have hsum :
      1 + D.qsSlope (1 : Fin 4) + D.qsSlope (2 : Fin 4) +
        D.qsSlope (3 : Fin 4) = 0 := by
    rw [hR, hS]
    linear_combination hQoneZero
  have hdegEq :=
    D.qs_outside_ordinaryDegree_eq_facet_of_direction_sum_zero
      ha hb hcontactScale hBal hcontact hsum
  omega

set_option maxHeartbeats 4000000 in
/-- The affine RR certificate attached to a two-fixed genuine `qs` first
contact is contradictory.  This command contains the expensive certificate
elaboration separately from the elementary first-contact arithmetic above. -/
private theorem qs_two_fixed_affine_terminal_impossible
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0)
    (hthree : MvRankThreeOnFacet .qs D.facetExponent)
    (hR : D.qsSlope (2 : Fin 4) = 0)
    (hS : D.qsSlope (3 : Fin 4) = 0)
    (hQ : D.qsSlope (1 : Fin 4) ≠ 0)
    (hQone : D.qsSlope (1 : Fin 4) + 1 ≠ 0) :
    False := by
  have hfacet := mvRankThreeOnFacet_qs hthree
  have hA : 0 < D.facetExponent (1 : Fin 4) := hfacet.2.1
  have hB : 0 < D.facetExponent (2 : Fin 4) := hfacet.2.2.1
  have hC : 0 < D.facetExponent (3 : Fin 4) := hfacet.2.2.2
  have hphiDeg : 0 < D.qsCoefficientPolynomial.natDegree :=
    D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact
  have hphi0 : D.qsCoefficientPolynomial.coeff 0 ≠ 0 :=
    D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact

  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  have hdetL : hessianDeterminant L.polynomial = 0 := by
    simpa [L] using
      D.qsAffineLineData_hessian_zero
        ha hb hcontactScale hBal hcontact hzero
  have hcertRaw :=
    HC4.RationalRigidity.hasRankThreePolynomialTerminalCertificate_of_affine_line
      L hA hB hC (by decide) hphiDeg hphi0 hdetL
  have hcert :
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := D.qsCoefficientPolynomial)
        ((D.facetExponent 1 : ℕ) : K)
        ((D.facetExponent 2 : ℕ) : K)
        ((D.facetExponent 3 : ℕ) : K)
        (1 : K)
        (D.qsSlope (1 : Fin 4)) 0 0 := by
    simpa [L, hR, hS] using hcertRaw

  exact HC4.RationalRigidity.rankThree_terminal_two_fixed_impossible
    hA hB hC (by decide) hphiDeg hphi0 hcert hQ hQone

/-- **The genuine `qs` rank-three first-contact branch is contradictory.** -/
theorem CrossFacetInitialData.qs_rankThree_firstContact_impossible
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (hcontactBump : 0 < contactBump)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel)
    (hzero : hessianDeterminant F = 0)
    (hthree : MvRankThreeOnFacet .qs D.facetExponent) :
    False := by
  have htransition := D.qs_rankThree_terminal_transition_pr
    ha hb hcontactScale hcontactBump hBal hcontact hzero hthree
  have hR : D.qsSlope (2 : Fin 4) = 0 := htransition.1
  have hS : D.qsSlope (3 : Fin 4) = 0 := htransition.2.1
  have hQ := qs_remainingSlope_ne_zero_of_two_fixed
    ha hb hcontactScale hcontactBump D hBal hcontact hR hS
  have hQone := qs_remainingSlope_add_one_ne_zero_of_two_fixed
    ha hb hcontactScale hcontactBump D hBal hcontact hR hS
  exact qs_two_fixed_affine_terminal_impossible
    ha hb hcontactScale D hBal hcontact hzero hthree hR hS hQ hQone

end

end HC4.Newton
