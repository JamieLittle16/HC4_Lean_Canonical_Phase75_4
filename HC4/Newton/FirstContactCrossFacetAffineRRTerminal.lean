import HC4.Newton.FirstContactCrossFacetAffineRRReconstruction
import HC4.RationalRigidity.RankThreeAffineLineTerminal
import HC4.RationalRigidity.RankThreeAffineTerminalBoundaryStratum
import HC4.RationalRigidity.RankThreeTerminalBinomialNormalForm
import HC4.RationalRigidity.RankThreeTerminalDirectionSplit
import HC4.RationalRigidity.RankThreeSingleDirectionRefinement
import HC4.RationalRigidity.RankThreeBalancedDegreeOneImpossible
import Mathlib.Tactic

/-!
# A18.5.68: the canonical rank-three cross-facet branch enters affine RR

A18.5.67 reconstructs the exact `qs` cross-facet face as a genuine
`RankThreeAffineLineData` polynomial.  Thus, when the certified facet endpoint
is rank three, every hypothesis of the mature affine RationalRigidity terminal
theorem is literal: the three base coordinates are positive, the omitted step
is `1`, the coefficient polynomial is nonconstant with nonzero constant term,
and the reconstructed affine polynomial has zero Hessian determinant.

This file packages that terminal certificate and retains toric balance at its
far supported exponent.  It also removes the degree-one branch honestly.  In
degree one the general affine line is automatically the old length-one honest
segment, so the already-green balanced degree-one contradiction applies with
no divisibility hypothesis.  The remaining scalar terminal alternatives are
then refined to two fixed transverse directions or ordinary-degree
preservation.
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

/-- Far endpoint stratum of the exact rank-three cross-facet terminal. -/
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

/-- The full affine terminal normal form is available on the rank-three
cross-facet branch. -/
noncomputable def CrossFacetInitialData.qs_rankThree_binomialNormalForm
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
    HC4.RationalRigidity.RankThreeTerminalBinomialNormalForm
      (D.qsAffineLineData ha hb hcontactScale hBal hcontact) := by
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  exact HC4.RationalRigidity.rankThreeTerminal_binomialNormalForm
    (D.qsAffineLineData ha hb hcontactScale hBal hcontact)
    hA hB hC (by decide)
    (D.qsCoefficientPolynomial_natDegree_pos
      ha hb hcontactScale hBal hcontact)
    (D.qsCoefficientPolynomial_coeff_zero_ne
      ha hb hcontactScale hBal hcontact)
    (D.qsAffineLineData_hessian_zero
      ha hb hcontactScale hBal hcontact hzero)

/-- In coefficient degree one the affine support is literally a length-one
honest rank-three segment, so the existing balanced degree-one contradiction
applies without any higher-degree divisibility assumption. -/
theorem CrossFacetInitialData.qs_rankThree_degreeOne_impossible
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
    (hdeg : D.qsCoefficientPolynomial.natDegree = 1) : False := by
  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  let u2 : ℕ := L.exponent 1 (1 : Fin 4)
  let u3 : ℕ := L.exponent 1 (2 : Fin 4)
  let u4 : ℕ := L.exponent 1 (3 : Fin 4)
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  have hnormal := D.qs_rankThree_binomialNormalForm
    ha hb hcontactScale hBal hcontact hzero hthree
  have hphi1 : D.qsCoefficientPolynomial.coeff 1 ≠ 0 :=
    hnormal.first_coefficient_ne_zero
  have h1mem : 1 ∈ D.qsCoefficientPolynomial.support :=
    Polynomial.mem_support_iff.mpr hphi1
  have h1exists := D.exists_faceExponent_of_qsCoefficientPolynomial_mem h1mem
  have h1spec := D.qsExponentAt_spec h1exists
  have hL1mem : L.exponent 1 ∈ D.face.support := by
    rw [show L.exponent 1 = D.qsExponentAt 1 by simp [L]]
    exact h1spec.1
  have hL1zero : L.exponent 1 (0 : Fin 4) = 1 := by
    have hz := L.exponent_zero_eq h1mem
    simpa using hz

  have hstartExp :
      rankThreeLineExponentFinsupp
        (D.facetExponent 1) (D.facetExponent 2) (D.facetExponent 3)
        1 u2 u3 u4 1 0 = D.facetExponent := by
    ext k
    fin_cases k <;>
      simp [rankThreeLineExponentFinsupp_apply, D.facet_coordinate_zero]

  have hendExp :
      rankThreeLineExponentFinsupp
        (D.facetExponent 1) (D.facetExponent 2) (D.facetExponent 3)
        1 u2 u3 u4 1 1 = L.exponent 1 := by
    ext k
    fin_cases k <;>
      simp [rankThreeLineExponentFinsupp_apply, u2, u3, u4, hL1zero]

  have hsupp : IsSupportedOnRankThreeLine
      (D.facetExponent 1) (D.facetExponent 2) (D.facetExponent 3)
      1 u2 u3 u4 1 D.face := by
    intro d hd
    have hidx : d (0 : Fin 4) ∈ D.qsCoefficientPolynomial.support :=
      D.qsCoefficientPolynomial_mem_of_face_mem
        ha hb hcontactScale hBal hcontact hd
    have hle : d (0 : Fin 4) ≤ 1 := by
      rw [← hdeg]
      exact Polynomial.le_natDegree_of_mem_supp _ hidx
    have hdExp : L.exponent (d (0 : Fin 4)) = d := by
      rw [show L.exponent (d (0 : Fin 4)) =
          D.qsExponentAt (d (0 : Fin 4)) by simp [L]]
      exact D.qsExponentAt_eq_of_face_mem
        ha hb hcontactScale hBal hcontact hd
    rcases Nat.eq_zero_or_pos (d (0 : Fin 4)) with hd0 | hdpos
    · refine ⟨0, by decide, ?_⟩
      have hdfacet : d = D.facetExponent := by
        exact D.qs_support_eq_of_zeroCoordinate_eq
          ha hb hcontactScale hBal hcontact hd D.facet_mem_face
          (by simpa [hd0, D.facet_coordinate_zero])
      rw [hdfacet]
      exact hstartExp.symm
    · have hd1 : d (0 : Fin 4) = 1 := by omega
      refine ⟨1, by decide, ?_⟩
      have hdExp1 : L.exponent 1 = d := by simpa [hd1] using hdExp
      exact hdExp1.symm.trans hendExp.symm

  have hstart :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          (D.facetExponent 1) (D.facetExponent 2) (D.facetExponent 3)
          1 u2 u3 u4 1 0) D.face ≠ 0 := by
    rw [hstartExp]
    exact MvPolynomial.mem_support_iff.mp D.facet_mem_face

  have hend :
      MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          (D.facetExponent 1) (D.facetExponent 2) (D.facetExponent 3)
          1 u2 u3 u4 1 1) D.face ≠ 0 := by
    rw [hendExp]
    exact MvPolynomial.mem_support_iff.mp hL1mem

  exact HC4.RationalRigidity.supported_balanced_rankThree_degreeOne_impossible
    (K := K) ha hb hA hB hC (by decide)
    (D.balanced hBal) hsupp hstart hend (D.hessian_zero hzero)

/-- After removing degree one and refining each single zero-direction branch,
the higher-degree affine terminal has two fixed transverse directions or
preserves ordinary degree. -/
theorem CrossFacetInitialData.qs_rankThree_refinedTerminalSplit
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
    ((D.qsSlope (1 : Fin 4) = 0 ∧ D.qsSlope (2 : Fin 4) = 0) ∨
     (D.qsSlope (1 : Fin 4) = 0 ∧ D.qsSlope (3 : Fin 4) = 0) ∨
     (D.qsSlope (2 : Fin 4) = 0 ∧ D.qsSlope (3 : Fin 4) = 0) ∨
     1 + D.qsSlope (1 : Fin 4) + D.qsSlope (2 : Fin 4) +
       D.qsSlope (3 : Fin 4) = 0) := by
  rcases D.qs_rankThree_endpoint_coordinates hthree with
    ⟨_hzero0, hA, hB, hC⟩
  have hdeg := D.qsCoefficientPolynomial_natDegree_pos
    ha hb hcontactScale hBal hcontact
  have hphi0 := D.qsCoefficientPolynomial_coeff_zero_ne
    ha hb hcontactScale hBal hcontact
  have hcert := D.qs_rankThree_terminalCertificate
    ha hb hcontactScale hBal hcontact hzero hthree
  have hsplit := HC4.RationalRigidity.rankThree_terminal_degreeOne_or_directionDegenerate
    (K := K) hA hB hC (by decide) hdeg hphi0 hcert
  rcases hsplit with hD | hQ | hR | hS | hhom
  · exact False.elim
      (D.qs_rankThree_degreeOne_impossible
        ha hb hcontactScale hBal hcontact hzero hthree hD)
  · rcases HC4.RationalRigidity.rankThree_terminal_Q_zero_refines
      (K := K) hA hB hC (by decide) hdeg hphi0 hcert hQ with
      hR | hS | hsum
    · exact Or.inl ⟨hQ, hR⟩
    · exact Or.inr (Or.inl ⟨hQ, hS⟩)
    · exact Or.inr (Or.inr (Or.inr (by simpa [hQ] using hsum)))
  · rcases HC4.RationalRigidity.rankThree_terminal_R_zero_refines
      (K := K) hA hB hC (by decide) hdeg hphi0 hcert hR with
      hQ | hS | hsum
    · exact Or.inl ⟨hQ, hR⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hR, hS⟩))
    · exact Or.inr (Or.inr (Or.inr (by simpa [hR] using hsum)))
  · rcases HC4.RationalRigidity.rankThree_terminal_S_zero_refines
      (K := K) hA hB hC (by decide) hdeg hphi0 hcert hS with
      hQ | hR | hsum
    · exact Or.inr (Or.inl ⟨hQ, hS⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hR, hS⟩))
    · exact Or.inr (Or.inr (Or.inr (by simpa [hS] using hsum)))
  · exact Or.inr (Or.inr (Or.inr hhom))

end

end HC4.Newton