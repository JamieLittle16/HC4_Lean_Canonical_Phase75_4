import HC4.Newton.FirstContactCrossFacetExtremeRayNormalForm
import Mathlib.Tactic

/-!
# Positive normal form of the genuine first-contact extreme-ray exit

The strengthened first-contact exit retains nonlinear support on the exact
singular carrier.  Consequently its selected `.qs` extreme-ray endpoint has
ordinary degree at least three, so the ray multiplier is strictly positive.

This packages the last boundary-classification step before complementary-edge
recognition: every genuine balanced `.qs` first contact exits at a positive
`q`-ray or positive `s`-ray endpoint.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Complete first-contact exit with the selected facet endpoint normalized to
one of the two positive rays adjacent to `.qs`. -/
theorem exists_qs_firstNonfacet_crossFacet_positiveExtremeRay
    {a b m : ℕ} {psi : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m psi)
    (htop : TopDegreeOnFacet .qs m psi)
    (hattained : ∃ v ∈ psi.support, ordinaryDegree4 v = m)
    (hout : HasNonlinearOutsideFacet .qs psi)
    (hlow : LowDegreeTameAtFacet .qs psi)
    (hBal : HasBalancedMvSupport a b psi)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere psi) :
    ∃ (scale bump : ℕ) (G : MvPolynomial (Fin 4) K)
      (D : CrossFacetInitialData G
        (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)),
      0 < scale ∧
      0 < bump ∧
      hessianDeterminant G = 0 ∧
      HasBalancedMvSupport a b G ∧
      (∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d) ∧
      ((∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) := by
  rcases exists_qs_firstNonfacet_crossFacet_extremeRay_nonlinear
      ha hb hcop hm hdeg htop hattained hout hlow hBal hMA with
    ⟨d₀, scale, bump, G, hG, hd₀G, hd₀deg, hscale, hbump,
      hzero, hnot, hGBal, hnonlinear, D, H, hAdj, hRay⟩
  have hfacetDeg : 3 ≤ ordinaryDegree4 D.facetExponent :=
    hnonlinear D.facetExponent D.facet_mem_face
  have hnormal :=
    D.qs_extremeRay_facet_coordinates_pos hAdj hRay hfacetDeg
  exact ⟨scale, bump, G, D, hscale, hbump, hzero, hGBal,
    hnonlinear, hnormal⟩



/-- Positive extreme-ray exit with the exact first-contact equation retained.

This is the assembly-facing version needed to expose the opposite endpoint of
the honest cross-facet line.  No new geometry is asserted: the contact equation
is inherited directly from the exact scaled-contact initial form. -/
theorem exists_qs_firstNonfacet_crossFacet_positiveExtremeRay_withContact
    {a b m : ℕ} {psi : MvPolynomial (Fin 4) K}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m psi)
    (htop : TopDegreeOnFacet .qs m psi)
    (hattained : ∃ v ∈ psi.support, ordinaryDegree4 v = m)
    (hout : HasNonlinearOutsideFacet .qs psi)
    (hlow : LowDegreeTameAtFacet .qs psi)
    (hBal : HasBalancedMvSupport a b psi)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere psi) :
    ∃ (scale bump : ℕ) (G : MvPolynomial (Fin 4) K)
      (D : CrossFacetInitialData G
        (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4)),
      0 < scale ∧
      0 < bump ∧
      hessianDeterminant G = 0 ∧
      HasBalancedMvSupport a b G ∧
      (∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d) ∧
      (∀ d ∈ G.support,
        scaledContactExponentWeight (0 : Fin 4) scale bump d =
          ((scale * m : ℕ) : ℤ)) ∧
      ((∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = n ∧
          D.facetExponent 2 = n ∧
          D.facetExponent 3 = 0) ∨
        (∃ n : ℕ, 0 < n ∧
          D.facetExponent 0 = 0 ∧
          D.facetExponent 1 = a * n ∧
          D.facetExponent 2 = 0 ∧
          D.facetExponent 3 = b * n)) := by
  rcases exists_qs_firstNonfacet_crossFacet_extremeRay_nonlinear
      ha hb hcop hm hdeg htop hattained hout hlow hBal hMA with
    ⟨d₀, scale, bump, G, hG, hd₀G, hd₀deg, hscale, hbump,
      hzero, hnot, hGBal, hnonlinear, D, H, hAdj, hRay⟩
  have hsupports := firstContactCarrier_crossFacet_supports
    (F := .qs) (m := m) (scale := scale) (bump := bump)
    htop hattained hG hnot
  have hcontact :
      ∀ d ∈ G.support,
        scaledContactExponentWeight (0 : Fin 4) scale bump d =
          ((scale * m : ℕ) : ℤ) := by
    simpa [facetOmittedCoordinate] using hsupports.2.2
  have hfacetDeg : 3 ≤ ordinaryDegree4 D.facetExponent :=
    hnonlinear D.facetExponent D.facet_mem_face
  have hnormal :=
    D.qs_extremeRay_facet_coordinates_pos hAdj hRay hfacetDeg
  exact ⟨scale, bump, G, D, hscale, hbump, hzero, hGBal,
    hnonlinear, hcontact, hnormal⟩
end

end HC4.Newton
