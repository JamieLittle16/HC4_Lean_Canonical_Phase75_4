import HC4.Newton.FirstContactCrossFacetAffineRRTerminal
import HC4.RationalRigidity.RankThreeAffineTerminalScalarData

/-!
# A18.5.73a.5: cache the cross-facet terminal as nondependent scalar data

A18.5.68 already constructs the expensive affine terminal certificate.  This
adapter copies that compiled certificate and its elementary endpoint side
conditions into `RankThreeAffineTerminalScalarData`.  The resulting object has
no dependent record projections and can be consumed cheaply by first-contact
code.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Cache the exact `qs` rank-three terminal in the small scalar RR interface.
No two-fixed hypotheses are needed at this stage.  This is a theorem rather
than a reducible definition, so downstream elaboration treats the expensive
construction as opaque. -/
theorem CrossFacetInitialData.qs_rankThree_terminalScalarData
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
    (hthree : MvRankThreeOnFacet .qs D.facetExponent) :
    HC4.RationalRigidity.RankThreeAffineTerminalScalarData
      (D.facetExponent 1) (D.facetExponent 2) (D.facetExponent 3) 1
      (D.qsSlope (1 : Fin 4))
      (D.qsSlope (2 : Fin 4))
      (D.qsSlope (3 : Fin 4))
      D.qsCoefficientPolynomial := by
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  exact {
    A_pos := hA
    B_pos := hB
    C_pos := hC
    P_pos := by decide
    phi_degree_pos := D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact
    phi_coeff_zero_ne := D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact
    certificate := by
      simpa only [Nat.cast_one] using
        (D.qs_rankThree_terminalCertificate
          ha hb hcontactScale hBal hcontact hzero hthree)
  }

end

end HC4.Newton
