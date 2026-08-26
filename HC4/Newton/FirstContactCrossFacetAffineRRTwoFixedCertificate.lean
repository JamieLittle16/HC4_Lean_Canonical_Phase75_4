import HC4.Newton.FirstContactCrossFacetAffineRRTerminal
import HC4.RationalRigidity.RankThreeAffineTwoFixedImpossible
import Mathlib.Tactic

/-!
# A18.5.73a.1: compact two-fixed affine terminal certificate

A18.5.68 already performs the expensive conversion from the exact cross-facet
line to `HasRankThreePolynomialTerminalCertificate`.  The surviving genuine
first-contact branch later proves that the last two affine slopes vanish.

This file specializes that certificate once and packages every remaining
RationalRigidity input behind a small, presentation-free record.  Downstream
first-contact code therefore never needs to elaborate the full dependent
cross-facet construction while invoking the final two-fixed contradiction.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The compact algebraic payload of a rank-three affine terminal with its last
two transverse directions fixed.  It contains exactly the inputs consumed by
A18.5.73a and no cross-facet presentation data. -/
structure QsTwoFixedTerminalData
    (Q : K) (phi : Polynomial K) : Type where
  A : ℕ
  B : ℕ
  C : ℕ
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C
  phi_degree_pos : 0 < phi.natDegree
  phi_coeff_zero_ne : phi.coeff 0 ≠ 0
  certificate :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := phi)
      (A : K) (B : K) (C : K) (1 : K) Q 0 0

/-- A compact two-fixed terminal payload is impossible as soon as the one
remaining slope is neither zero nor `-1`. -/
theorem QsTwoFixedTerminalData.impossible
    {Q : K} {phi : Polynomial K}
    (data : QsTwoFixedTerminalData Q phi)
    (hQ : Q ≠ 0)
    (hQone : Q + 1 ≠ 0) :
    False := by
  exact HC4.RationalRigidity.rankThree_terminal_two_fixed_impossible
    data.A_pos data.B_pos data.C_pos (by decide)
    data.phi_degree_pos data.phi_coeff_zero_ne
    data.certificate hQ hQone

/-- Specialize the already-compiled A18.5.68 terminal certificate when the
second and third transverse affine slopes are fixed. -/
theorem CrossFacetInitialData.qs_rankThree_terminalCertificate_two_fixed
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
    (hS : D.qsSlope (3 : Fin 4) = 0) :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := D.qsCoefficientPolynomial)
      ((D.facetExponent 1 : ℕ) : K)
      ((D.facetExponent 2 : ℕ) : K)
      ((D.facetExponent 3 : ℕ) : K)
      (1 : K)
      (D.qsSlope (1 : Fin 4)) 0 0 := by
  have hcert :
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := D.qsCoefficientPolynomial)
        ((D.facetExponent 1 : ℕ) : K)
        ((D.facetExponent 2 : ℕ) : K)
        ((D.facetExponent 3 : ℕ) : K)
        (1 : K)
        (D.qsSlope (1 : Fin 4))
        (D.qsSlope (2 : Fin 4))
        (D.qsSlope (3 : Fin 4)) :=
    D.qs_rankThree_terminalCertificate
      ha hb hcontactScale hBal hcontact hzero hthree
  simpa only [hR, hS] using hcert

set_option maxHeartbeats 800000 in
/-- Collapse all expensive cross-facet elaboration into the compact algebraic
payload used by the final first-contact contradiction. -/
noncomputable def CrossFacetInitialData.qs_rankThree_twoFixedTerminalData
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
    (hS : D.qsSlope (3 : Fin 4) = 0) :
    QsTwoFixedTerminalData
      (D.qsSlope (1 : Fin 4)) D.qsCoefficientPolynomial := by
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  exact {
    A := D.facetExponent 1
    B := D.facetExponent 2
    C := D.facetExponent 3
    A_pos := hA
    B_pos := hB
    C_pos := hC
    phi_degree_pos := D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact
    phi_coeff_zero_ne := D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact
    certificate := D.qs_rankThree_terminalCertificate_two_fixed
      ha hb hcontactScale hBal hcontact hzero hthree hR hS
  }

end

end HC4.Newton
