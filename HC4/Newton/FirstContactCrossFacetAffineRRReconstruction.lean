import HC4.Newton.FirstContactCrossFacetAffineRR
import Mathlib.Tactic

/-!
# A18.5.67b: exact reconstruction of the cross-facet affine RR polynomial

A18.5.67a reindexes the canonical `qs` cross-facet face by its literal omitted
coordinate and constructs `RankThreeAffineLineData`.  This file proves that the
associated honest multivariate polynomial is not merely support-equivalent to
the Newton face: it is exactly that face.

The proof is coefficientwise.  On genuine face support, coordinate-zero
injectivity makes `d 0` the unique coefficient index contributing to exponent
`d`.  Off support, every supported univariate index reconstructs an actual face
exponent, so no affine term can contribute.  Consequently the Hessian-zero
identity already carried by `CrossFacetInitialData` transfers verbatim to the
mature affine RationalRigidity object.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The exponent function stored by the canonical affine RR package is
literally the support reindexing from A18.5.67a. -/
@[simp] theorem CrossFacetInitialData.qsAffineLineData_exponent
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
    (n : ℕ) :
    (D.qsAffineLineData ha hb hcontactScale hBal hcontact).exponent n =
      D.qsExponentAt n := by
  rfl

/-- **Exact affine-RR reconstruction.**  The honest multivariate polynomial
attached to the canonical affine-line data is exactly the exposed cross-facet
face. -/
theorem CrossFacetInitialData.qsAffineLineData_polynomial_eq_face
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
    (D.qsAffineLineData ha hb hcontactScale hBal hcontact).polynomial =
      D.face := by
  classical
  let L := D.qsAffineLineData ha hb hcontactScale hBal hcontact
  change L.polynomial = D.face
  apply MvPolynomial.ext
  intro d
  simp only [RankThreeAffineLineData.polynomial, Polynomial.sum_def]
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d ∈ D.face.support
  · have hidx : d (0 : Fin 4) ∈ D.qsCoefficientPolynomial.support :=
      D.qsCoefficientPolynomial_mem_of_face_mem
        ha hb hcontactScale hBal hcontact hd
    have hexp : L.exponent (d (0 : Fin 4)) = d := by
      rw [show L.exponent (d (0 : Fin 4)) = D.qsExponentAt (d (0 : Fin 4)) by
        simp [L]]
      exact D.qsExponentAt_eq_of_face_mem
        ha hb hcontactScale hBal hcontact hd
    have hcoeff :
        D.qsCoefficientPolynomial.coeff (d (0 : Fin 4)) =
          MvPolynomial.coeff d D.face :=
      D.coeff_qsCoefficientPolynomial_of_mem
        ha hb hcontactScale hBal hcontact hd
    rw [Finset.sum_eq_single (d (0 : Fin 4))]
    · rw [L.term_eq_monomial]
      simp [hexp, hcoeff]
    · intro n hn hnd
      have hne : L.exponent n ≠ d := by
        intro heq
        have h0 := congrArg
          (fun e : Fin 4 →₀ ℕ => e (0 : Fin 4)) heq
        have hn0 : L.exponent n (0 : Fin 4) = n := by
          have hz := L.exponent_zero_eq hn
          simpa using hz
        rw [hn0] at h0
        exact hnd h0
      rw [L.term_eq_monomial]
      simp [hne]
    · intro hnot
      exact (hnot hidx).elim
  · have hd0 : MvPolynomial.coeff d D.face = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [hd0]
    apply Finset.sum_eq_zero
    intro n hn
    have hex := D.exists_faceExponent_of_qsCoefficientPolynomial_mem hn
    have hspec := D.qsExponentAt_spec hex
    have hLmem : L.exponent n ∈ D.face.support := by
      rw [show L.exponent n = D.qsExponentAt n by simp [L]]
      exact hspec.1
    have hne : L.exponent n ≠ d := by
      intro heq
      apply hd
      simpa [heq] using hLmem
    rw [L.term_eq_monomial]
    simp [hne]

/-- Hessian singularity transfers exactly from the cross-facet face to the
affine RationalRigidity realisation. -/
theorem CrossFacetInitialData.qsAffineLineData_hessian_zero
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
    (hzero : hessianDeterminant F = 0) :
    hessianDeterminant
      (D.qsAffineLineData ha hb hcontactScale hBal hcontact).polynomial = 0 := by
  rw [D.qsAffineLineData_polynomial_eq_face
    ha hb hcontactScale hBal hcontact]
  exact D.hessian_zero hzero

end

end HC4.Newton
