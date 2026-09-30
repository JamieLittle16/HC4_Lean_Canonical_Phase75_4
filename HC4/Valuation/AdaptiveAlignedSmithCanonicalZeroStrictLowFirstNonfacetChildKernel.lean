import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import HC4.RationalRigidity.FirstContactCrossFacetFarRankThreeAffine
import Mathlib.Tactic

/-!
# Exact child-face kernel on the retained strict-low .qs first-contact packet

The valuation stack already constructs the honest lower first-contact packet
`AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs`
without requiring low-degree tameness: the strict-low source supplies the
two-outside comparison used by the strengthened selector.

The affine RationalRigidity endgame is now stronger than the older boundary
classification.  Once torus balance of the represented source is available,
the *same retained packet* has an exact secondary child face with a literal
coordinate kernel.  No first-contact selector is rerun here and no new
Schur/Rees geometry is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **Retained .qs first contact -> literal child-face coordinate kernel.**

This theorem consumes the exact valuation-side first-contact packet rather than
re-running the rooted Newton selector.  Hence it also applies to the strict-low
`firstNonfacetCrossFacetData_qs` construction, whose low-degree control comes
from the two-outside comparison rather than `LowDegreeTameAtFacet`.

The actual far endpoint is retained as `R`; the only surviving affine-RR
outcome is the coordinate kernel on the exact secondary face
`C.crossFacet.face`. -/
theorem qs_childKernel_of_balanced
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hBal :
      HasBalancedMvSupport a b
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)) :
    ∃ (R : CrossFacetFarBoundaryData (a := a) (b := b) C.crossFacet)
      (kernelCoordinate : Fin 4),
      MvPolynomial.pderiv kernelCoordinate C.crossFacet.face = 0 := by
  have hFaceBal : HasBalancedMvSupport a b C.face := by
    rw [C.face_eq]
    exact hBal.initialForm _ _

  have hcontact :
      ∀ d ∈ C.face.support,
        scaledContactExponentWeight (0 : Fin 4) C.scale C.bump d =
          ((C.scale * T.topFace.degree : ℕ) : ℤ) := by
    simpa [facetOmittedCoordinate] using C.contact_eq

  have hfacetDeg :
      3 ≤ ordinaryDegree4 C.crossFacet.facetExponent :=
    C.support_degree_ge_three
      C.crossFacet.facetExponent C.crossFacet.facet_mem

  have hexit :=
    C.crossFacet.qs_firstContact_endpoint_extremeRay
      ha hb hcop C.scale_pos C.bump_pos hFaceBal hcontact C.hessian_zero
  rcases hexit.2 with ⟨H, hAdj, hRay⟩

  have hnear :=
    C.crossFacet.qs_extremeRay_facet_coordinates_pos
      hAdj hRay hfacetDeg

  let R : CrossFacetFarBoundaryData (a := a) (b := b) C.crossFacet :=
    C.crossFacet.farBoundaryData
      ha hb hcop C.scale_pos hFaceBal hcontact C.hessian_zero
      C.support_degree_ge_three

  rcases
      HC4.RationalRigidity.CrossFacetFarBoundaryData.kernel_of_positiveFirstContact
        R ha hb hcop C.scale_pos C.bump_pos C.crossFacet
        hFaceBal hcontact C.hessian_zero hnear with
    ⟨kernelCoordinate, hkernel⟩
  exact ⟨R, kernelCoordinate, hkernel⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
