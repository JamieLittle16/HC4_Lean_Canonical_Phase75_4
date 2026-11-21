import HC4.Newton.FirstContactCrossFacetAffineRRTerminal
import HC4.RationalRigidity.RankThreeTerminalFacetTransition
import Mathlib.Tactic

/-!
# A18.5.68b: finite terminal split for the exact cross-facet face

Once the exact `qs` cross-facet face has entered the mature affine
RationalRigidity terminal, no further scalar analysis is required.  A18.5.68a
already removes the degree-one branch and refines every single vanishing slope
to either two vanishing transverse slopes or ordinary-degree preservation.
This file only projects that stronger result to the legacy five-way interface
and records the far boundary coordinate supplied by the terminal facet theorem.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The exact rank-three cross-facet terminal has the mature five-way affine
direction split.  This is now a cheap projection of the stronger refined split
proved in A18.5.68a; in particular no terminal certificate is reconstructed
here. -/
theorem CrossFacetInitialData.qs_rankThree_terminalDirectionSplit
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
    D.qsCoefficientPolynomial.natDegree = 1 ∨
      D.qsSlope (1 : Fin 4) = 0 ∨
      D.qsSlope (2 : Fin 4) = 0 ∨
      D.qsSlope (3 : Fin 4) = 0 ∨
      1 + D.qsSlope (1 : Fin 4) + D.qsSlope (2 : Fin 4) +
        D.qsSlope (3 : Fin 4) = 0 := by
  rcases D.qs_rankThree_refinedTerminalSplit
      ha hb hcontactScale hBal hcontact hzero hthree with
    h12 | h13 | h23 | hhom
  · exact Or.inr (Or.inl h12.1)
  · exact Or.inr (Or.inl h13.1)
  · exact Or.inr (Or.inr (Or.inl h23.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hhom)))

/-- The far exponent of the exact rank-three cross-facet terminal has positive
omitted coordinate and vanishes in one transverse coordinate. -/
theorem CrossFacetInitialData.qs_rankThree_terminalTop_transverse_zero
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
    let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
    L.exponent D.qsCoefficientPolynomial.natDegree (0 : Fin 4) =
        D.qsCoefficientPolynomial.natDegree ∧
      (L.exponent D.qsCoefficientPolynomial.natDegree (1 : Fin 4) = 0 ∨
       L.exponent D.qsCoefficientPolynomial.natDegree (2 : Fin 4) = 0 ∨
       L.exponent D.qsCoefficientPolynomial.natDegree (3 : Fin 4) = 0) := by
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  have hdeg : 0 < D.qsCoefficientPolynomial.natDegree :=
    D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact
  have hphi0 : D.qsCoefficientPolynomial.coeff 0 ≠ 0 :=
    D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact
  have hdet : hessianDeterminant L.polynomial = 0 := by
    simpa [L] using
      (D.qsAffineLineData_hessian_zero
        ha hb hcontactScale hBal hcontact hzero)
  exact HC4.RationalRigidity.rankThreeTerminal_top_transverse_coordinate_zero
    L hA hB hC (by decide) hdeg hphi0 hdet

end

end HC4.Newton
