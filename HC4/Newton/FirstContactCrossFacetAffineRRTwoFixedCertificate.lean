import HC4.Newton.FirstContactCrossFacetAffineRRTerminal
import Mathlib.Tactic

/-!
# A18.5.73a.1: specialize the cached affine terminal certificate

A18.5.68 already performs the expensive conversion from the exact cross-facet
line to `HasRankThreePolynomialTerminalCertificate`.  The surviving genuine
first-contact branch later proves that the last two affine slopes vanish.

This tiny adapter performs that dependent specialization once, behind its own
opaque theorem boundary.  Downstream contradiction theorems can therefore
consume a certificate with literal slopes `(Q,0,0)` without asking the
elaborator to rewrite the full cross-facet construction again.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

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

end

end HC4.Newton
