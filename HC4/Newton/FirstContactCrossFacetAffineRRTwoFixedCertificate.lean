import HC4.Newton.FirstContactCrossFacetAffineRRTerminal
import HC4.RationalRigidity.RankThreeAffineTwoFixedImpossible
import Mathlib.Tactic

/-!
# A18.5.73a.1: compact two-fixed affine terminal certificate

A18.5.68 already performs the expensive conversion from the exact cross-facet
line to `HasRankThreePolynomialTerminalCertificate`.  The surviving genuine
first-contact branch later proves that the last two affine slopes vanish.

The important elaboration point is that we do **not** specialize the dependent
terminal certificate while it still mentions the full cross-facet datum.
Instead the compact record stores the original three-slope certificate together
with the two scalar equalities `R = 0` and `S = 0`.  Only its presentation-free
`impossible` method performs those two rewrites, in a tiny RationalRigidity
context.  This keeps the large cross-facet dependent term opaque.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The compact algebraic payload of a rank-three affine terminal whose last
two transverse directions are certified to be fixed.  The certificate itself
is kept in its original `(Q,R,S)` form so no dependent rewriting occurs in the
cross-facet layer. -/
structure QsTwoFixedTerminalData
    (Q : K) (phi : Polynomial K) : Type u where
  A : ℕ
  B : ℕ
  C : ℕ
  A_pos : 0 < A
  B_pos : 0 < B
  C_pos : 0 < C
  phi_degree_pos : 0 < phi.natDegree
  phi_coeff_zero_ne : phi.coeff 0 ≠ 0
  R : K
  S : K
  R_zero : R = 0
  S_zero : S = 0
  certificate :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := phi)
      (A : K) (B : K) (C : K) (1 : K) Q R S

/-- A compact two-fixed terminal payload is impossible as soon as the one
remaining slope is neither zero nor `-1`.

The only certificate specialization happens here, after all cross-facet
presentation data has disappeared from the type. -/
theorem QsTwoFixedTerminalData.impossible
    {Q : K} {phi : Polynomial K}
    (data : QsTwoFixedTerminalData Q phi)
    (hQ : Q ≠ 0)
    (hQone : Q + 1 ≠ 0) :
    False := by
  have hcert := data.certificate
  rw [data.R_zero, data.S_zero] at hcert
  exact HC4.RationalRigidity.rankThree_terminal_two_fixed_impossible
    data.A_pos data.B_pos data.C_pos (by decide)
    data.phi_degree_pos data.phi_coeff_zero_ne
    hcert hQ hQone

/-- Collapse the cross-facet terminal into the compact algebraic payload.
The already-compiled A18.5.68 certificate is copied verbatim; no dependent
specialization is performed here. -/
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
    R := D.qsSlope (2 : Fin 4)
    S := D.qsSlope (3 : Fin 4)
    R_zero := hR
    S_zero := hS
    certificate := D.qs_rankThree_terminalCertificate
      ha hb hcontactScale hBal hcontact hzero hthree
  }

end

end HC4.Newton
