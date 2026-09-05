import HC4.Newton.FirstContactCrossFacetAffineRRTerminal
import HC4.RationalRigidity.RankThreeAffineTwoFixedEqualitiesImpossible
import Mathlib.Tactic

/-!
# A18.5.73a.3: eliminate a cached two-fixed cross-facet terminal

A18.5.68 already owns the expensive construction of the affine terminal
certificate.  This adapter consumes that compiled theorem once and exposes a
single opaque Newton-level eliminator.  The first-contact theorem downstream
therefore never elaborates the certificate type, endpoint positivity, or
coefficient-polynomial side conditions.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 800000 in
/-- A cached `qs` affine RR terminal is impossible when the last two slopes
vanish and the remaining slope is neither zero nor `-1`. -/
theorem CrossFacetInitialData.qs_rankThree_twoFixed_terminal_impossible
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
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  exact HC4.RationalRigidity.rankThree_terminal_two_fixed_impossible_of_eq
    (K := K)
    hA hB hC (by decide)
    (D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact)
    (D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact)
    (D.qs_rankThree_terminalCertificate
      ha hb hcontactScale hBal hcontact hzero hthree)
    hR hS hQ hQone

end

end HC4.Newton
