import HC4.Newton.FirstNonfacetContact
import Mathlib.Tactic

/-!
# A18.5.32: first-contact support is genuinely nonlinear

The first-contact construction already proves that every low-degree HC4
monomial lies strictly below the selected contact level.  This file records
the exact support consequence needed by the terminal convex step: no monomial
of ordinary degree at most two survives in the contact initial form.

Thus every supported monomial of the genuine first-contact polynomial has
ordinary degree at least three.  In particular any subsequently exposed
singleton automatically satisfies the nonlinear hypothesis of
`InteriorVertex` / `ExposedBalancedBoundaryStratum`.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

/-- **Every monomial on a genuine HC4 contact face is nonlinear.** -/
theorem firstContact_initialForm_support_degree_ge_three
    {K : Type*} [CommRing K]
    {j : Fin 4} {scale bump m : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hscale : 0 < scale)
    (hbump : bump ≤ scale * (m - 3))
    (hlow : ∀ d ∈ psi.support, ordinaryDegree4 d < 3 → d j ≤ 1) :
    ∀ d ∈
        (initialForm (scaledContactWeight j scale bump)
          (scale * m : ℕ) psi).support,
      3 ≤ ordinaryDegree4 d := by
  intro d hd
  have hdPsi : d ∈ psi.support :=
    support_initialForm_subset
      (scaledContactWeight j scale bump) (scale * m : ℕ) psi hd
  have hcoeff :
      MvPolynomial.coeff d
        (initialForm (scaledContactWeight j scale bump)
          (scale * m : ℕ) psi) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hweight :
      Finsupp.weight (scaledContactWeight j scale bump) d =
        ((scale * m : ℕ) : ℤ) := by
    exact
      (initialForm_isWeightedHomogeneous
        (scaledContactWeight j scale bump) (scale * m : ℕ) psi) hcoeff
  by_contra hnot
  have hdeg2 : ordinaryDegree4 d ≤ 2 := by omega
  have hj : d j ≤ 1 := hlow d hdPsi (by omega)
  have hstrict :=
    lowDegree_below_scaled_contact
      hscale hdeg2 hj hbump hm
  rw [← weight_scaledContactWeight] at hstrict
  omega


/-- The nonlinear-support conclusion also holds with a pure quadratic square
in the bumped coordinate when the contact satisfies the stronger doubled-bump
margin. -/
theorem firstContact_initialForm_support_degree_ge_three_of_two_mul_bump_le
    {K : Type*} [CommRing K]
    {j : Fin 4} {scale bump m : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hscale : 0 < scale)
    (hbump : 2 * bump ≤ scale * (m - 3)) :
    ∀ d ∈
        (initialForm (scaledContactWeight j scale bump)
          (scale * m : ℕ) psi).support,
      3 ≤ ordinaryDegree4 d := by
  intro d hd
  have hdPsi : d ∈ psi.support :=
    support_initialForm_subset
      (scaledContactWeight j scale bump) (scale * m : ℕ) psi hd
  have hcoeff :
      MvPolynomial.coeff d
        (initialForm (scaledContactWeight j scale bump)
          (scale * m : ℕ) psi) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hweight :
      Finsupp.weight (scaledContactWeight j scale bump) d =
        ((scale * m : ℕ) : ℤ) := by
    exact
      (initialForm_isWeightedHomogeneous
        (scaledContactWeight j scale bump) (scale * m : ℕ) psi) hcoeff
  by_contra hnot
  have hdeg2 : ordinaryDegree4 d ≤ 2 := by omega
  have hj2 : d j ≤ 2 := by
    fin_cases j <;> simp [ordinaryDegree4] at hdeg2 ⊢ <;> omega
  have hstrict :=
    lowDegree_below_scaled_contact_of_two_mul_bump_le
      hscale hdeg2 hj2 hbump hm
  rw [← weight_scaledContactWeight] at hstrict
  omega


/-- **Strengthened genuine first-contact package.**

The selected first non-facet contact may be exported together with the fact
that every exponent of its exact initial form is nonlinear.  This is the
assembly-facing form needed by the final complementary-edge extraction. -/
theorem exists_singular_first_nonfacet_contact_with_nonlinear_support
    {K : Type*} [Field K] [CharZero K]
    {F : HC4.Toric.ToricFacet} {m : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m psi)
    (htop : TopDegreeOnFacet F m psi)
    (hout : HasNonlinearOutsideFacet F psi)
    (hlow : LowDegreeTameAtFacet F psi)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere psi) :
    ∃ (d₀ : Fin 4 →₀ ℕ) (scale bump : ℕ)
      (G : MvPolynomial (Fin 4) K),
      G = initialForm
          (scaledContactWeight (HC4.Toric.facetOmittedCoordinate F) scale bump)
          ((scale * m : ℕ) : ℤ) psi ∧
      d₀ ∈ G.support ∧
      3 ≤ ordinaryDegree4 d₀ ∧
      0 < d₀ (HC4.Toric.facetOmittedCoordinate F) ∧
      0 < scale ∧
      0 < bump ∧
      hessianDeterminant G = 0 ∧
      ¬ HC4.Polynomial.MvSupportOnFacet F G ∧
      (∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d) := by
  rcases exists_singular_first_nonfacet_contact
      hm hdeg htop hout hlow hMA with
    ⟨d₀, scale, bump, hdpsi, hddeg, hdpos, hscaleEq, hbumpEq,
      hscale, hbump, hbound, hzero, hdinit, hnot⟩
  let j := HC4.Toric.facetOmittedCoordinate F
  let G : MvPolynomial (Fin 4) K :=
    initialForm (scaledContactWeight j scale bump)
      ((scale * m : ℕ) : ℤ) psi
  have hcontact :
      scaledContactExponentWeight j scale bump d₀ =
        ((scale * m : ℕ) : ℤ) := by
    have hhom :=
      initialForm_isWeightedHomogeneous
        (scaledContactWeight j scale bump)
        ((scale * m : ℕ) : ℤ) psi
        (MvPolynomial.mem_support_iff.mp (by simpa [G] using hdinit))
    rw [weight_scaledContactWeight] at hhom
    exact hhom
  have hbumpBound : bump ≤ scale * (m - 3) := by
    apply bump_le_scale_mul_m_sub_three hscale
    · simpa [j] using hdpos
    · exact hddeg
    · exact hcontact
  have hlow' :
      ∀ d ∈ psi.support, ordinaryDegree4 d < 3 → d j ≤ 1 := by
    simpa [LowDegreeTameAtFacet, j] using hlow
  have hnonlinear :
      ∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d := by
    dsimp [G]
    exact firstContact_initialForm_support_degree_ge_three
      hm hscale hbumpBound hlow'
  refine ⟨d₀, scale, bump, G, rfl, ?_, hddeg, ?_,
    hscale, hbump, ?_, ?_, hnonlinear⟩
  · simpa [G] using hdinit
  · simpa [j] using hdpos
  · simpa [G] using hzero
  · simpa [G] using hnot

end

end HC4.Newton
