import HC4.Newton.FirstNonfacetContact
import HC4.Newton.InteriorVertex

/-!
# First non-facet contact with certified toric boundary vertices

Phase 56 constructed the first non-facet contact directly from finite support,
and Phase 58 proved that a nonlinear monomial exposed from any zero-Hessian
polynomial must lie on the toric boundary.  This module combines those two
results in the form used by the Newton-polygon step.

For a torus-balanced HC4 potential, we obtain a singular first-contact
polynomial which is still balanced, is not contained in the starting facet,
and whose every further exposed nonlinear singleton is on the boundary of the
invariant cone.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

/-- **Balanced first non-facet contact with boundary exposed vertices.** -/
theorem exists_singular_first_nonfacet_contact_with_boundary_vertices
    {K : Type*} [Field K] [CharZero K]
    {a b : ℕ} {F : ToricFacet} {m : ℕ}
    {ψ : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m ψ)
    (htop : TopDegreeOnFacet F m ψ)
    (hout : HasNonlinearOutsideFacet F ψ)
    (hlow : LowDegreeTameAtFacet F ψ)
    (hBal : HasBalancedMvSupport a b ψ)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere ψ) :
    ∃ (d₀ : Fin 4 →₀ ℕ) (scale bump : ℕ)
      (G : MvPolynomial (Fin 4) K),
      G = initialForm
          (scaledContactWeight (facetOmittedCoordinate F) scale bump)
          (scale * m : ℕ) ψ ∧
      d₀ ∈ G.support ∧
      3 ≤ ordinaryDegree4 d₀ ∧
      0 < scale ∧ 0 < bump ∧
      hessianDeterminant G = 0 ∧
      ¬ MvSupportOnFacet F G ∧
      HasBalancedMvSupport a b G ∧
      (∀ (w : Fin 4 → ℤ) (level : ℤ) (d : Fin 4 →₀ ℕ) (c : K),
        IsWeightLE w level G →
        initialForm w level G = MvPolynomial.monomial d c →
        c ≠ 0 → 3 ≤ ordinaryDegree4 d →
        MvExponentOnBoundary d) := by
  rcases exists_singular_first_nonfacet_contact
      hm hdeg htop hout hlow hMA with
    ⟨d₀, scale, bump, hdψ, hddeg, hdpos, hscaleEq, hbumpEq,
      hscale, hbump, hbound, hzero, hdG, hnotFacet⟩
  let G : MvPolynomial (Fin 4) K :=
    initialForm
      (scaledContactWeight (facetOmittedCoordinate F) scale bump)
      (scale * m : ℕ) ψ
  have hGBal : HasBalancedMvSupport a b G := by
    dsimp [G]
    exact hBal.initialForm _ _
  refine ⟨d₀, scale, bump, G, rfl, ?_, hddeg, hscale, hbump,
    ?_, ?_, hGBal, ?_⟩
  · simpa [G] using hdG
  · simpa [G] using hzero
  · simpa [G] using hnotFacet
  · intro w level d c hw hinit hc hdegMono
    apply exposed_monomial_on_boundary_of_zero_hessian
      (F := G) hw
    · simpa [G] using hzero
    · exact hinit
    · exact hc
    · exact hdegMono

end

end HC4.Newton
