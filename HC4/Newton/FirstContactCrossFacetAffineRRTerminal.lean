import HC4.Newton.FirstContactCrossFacetAffineRRReconstruction
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import HC4.RationalRigidity.RankThreeAffineTerminalBoundaryStratum
import Mathlib.Tactic

/-!
# A18.5.68a: the canonical rank-three cross-facet branch enters affine RR

A18.5.67a constructs the affine line data and A18.5.67b proves that its honest
multivariate polynomial is exactly the exposed cross-facet face.  Thus, when
the certified facet endpoint is genuinely rank three, every hypothesis of the
mature affine RationalRigidity terminal theorem is now literal:

* the three base coordinates are positive;
* the omitted-coordinate step is `1`;
* the coefficient polynomial has positive degree and nonzero constant term;
* the honest affine polynomial has zero Hessian determinant.

This file packages the resulting terminal certificate and retains toric
balance at the far supported exponent.  The latter lets the already-green
affine top-stratum theorem classify that endpoint without any new Newton
geometry.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- The canonical `qs` rank-three cross-facet line reaches the existing affine
RationalRigidity polynomial terminal certificate. -/
theorem CrossFacetInitialData.qs_rankThree_terminalCertificate
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
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := D.qsCoefficientPolynomial)
      ((D.facetExponent 1 : ℕ) : K)
      ((D.facetExponent 2 : ℕ) : K)
      ((D.facetExponent 3 : ℕ) : K)
      (1 : K)
      (D.qsSlope (1 : Fin 4))
      (D.qsSlope (2 : Fin 4))
      (D.qsSlope (3 : Fin 4)) := by
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
  exact HC4.RationalRigidity.hasRankThreePolynomialTerminalCertificate_of_affine_line
    L hA hB hC (by decide) hdeg hphi0 hdet

/-- The far coefficient index of the canonical affine line is represented by
an actual support exponent of the exposed face. -/
theorem CrossFacetInitialData.qsAffineLineData_top_mem_face_support
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
    L.exponent D.qsCoefficientPolynomial.natDegree ∈ D.face.support := by
  let phi := D.qsCoefficientPolynomial
  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  have hphi0 : phi.coeff 0 ≠ 0 := by
    dsimp [phi]
    exact D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact
  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphi0
  have htop : phi.natDegree ∈ phi.support := by
    rw [Polynomial.mem_support_iff]
    change phi.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hphi
  have hex := D.exists_faceExponent_of_qsCoefficientPolynomial_mem htop
  have hspec := D.qsExponentAt_spec hex
  dsimp [L]
  rw [D.qsAffineLineData_exponent
    ha hb hcontactScale hBal hcontact]
  simpa [phi] using hspec.1

/-- Toric balance is retained at the far supported exponent of the canonical
affine RR line. -/
theorem CrossFacetInitialData.qsAffineLineData_top_balanced
    {F : MvPolynomial (Fin 4) K}
    {a b contactScale contactBump : ℕ} {contactLevel : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hcontactScale : 0 < contactScale)
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    (hBal : HasBalancedMvSupport a b F)
    (hcontact : ∀ d ∈ F.support,
      scaledContactExponentWeight (0 : Fin 4)
        contactScale contactBump d = contactLevel) :
    let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
    IsBalancedExponent a b
      (L.exponent D.qsCoefficientPolynomial.natDegree) := by
  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  have hmem : L.exponent D.qsCoefficientPolynomial.natDegree ∈
      D.face.support := by
    simpa [L] using
      (D.qsAffineLineData_top_mem_face_support
        ha hb hcontactScale hBal hcontact)
  exact D.balanced hBal _ hmem

/-- **Far endpoint stratum of the exact rank-three cross-facet terminal.** -/
theorem CrossFacetInitialData.qs_rankThree_terminalTopStratum
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
    (hzero : hessianDeterminant F = 0)
    (hthree : MvRankThreeOnFacet .qs D.facetExponent) :
    let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
    HC4.RationalRigidity.RankThreeAffineTerminalTopStratum
      a b (L.exponent D.qsCoefficientPolynomial.natDegree) := by
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  have hdeg : 0 < D.qsCoefficientPolynomial.natDegree :=
    D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact
  have hphi0 : D.qsCoefficientPolynomial.coeff 0 ≠ 0 :=
    D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact
  have hcert := D.qs_rankThree_terminalCertificate
    ha hb hcontactScale hBal hcontact hzero hthree
  have htopBal : IsBalancedExponent a b
      (L.exponent D.qsCoefficientPolynomial.natDegree) := by
    simpa [L] using
      (D.qsAffineLineData_top_balanced
        ha hb hcontactScale hBal hcontact)
  exact HC4.RationalRigidity.rankThreeAffineTerminal_topStratum
    ha hb hcop L hA hB hC (by decide) hdeg hphi0 hcert htopBal

end

end HC4.Newton
