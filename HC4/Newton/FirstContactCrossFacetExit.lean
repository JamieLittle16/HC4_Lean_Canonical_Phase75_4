import HC4.Newton.FirstContactCrossFacetCarrier
import HC4.Newton.FirstContactCrossFacetEndpointTransition
import Mathlib.Tactic

/-!
# A18.5.71: the genuine first non-facet contact has a geometric exit

A18.5.70 proves that an attained top nonlinear degree supplies the missing
on-facet survivor in the exact first-contact carrier.  Together with the
outside survivor already present in the first-nonfacet theorem, this constructs
the honest secondary cross-facet face of A18.5.65c.

A18.5.69 can then be applied without any synthetic endpoint: the selected
endpoint is either already on an extreme ray adjacent to `qs`, or the far
endpoint of the exact affine RR realisation is rank three on `pr`.

The conclusion below deliberately forgets proof-dependent affine-line data and
returns only actual support geometry.  In the second branch the `pr` exponent
is certified to belong to the exact secondary face support.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **A18.5.71 genuine canonical first-contact exit.**

For a torus-balanced Monge--Ampère polynomial whose attained top nonlinear
degree lies on `qs` but whose nonlinear support is not confined there, the
genuine positive-bump first contact produces an exact cross-facet face with
one of two actual geometric exits:

* the selected `qs` endpoint already lies on an adjacent extreme ray; or
* an actual supported exponent of the exact secondary face is rank three on
  the adjacent `pr` facet.
-/
theorem exists_qs_firstNonfacet_crossFacet_exit
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
    ∃ (d₀ : Fin 4 →₀ ℕ) (scale bump : ℕ)
      (G : MvPolynomial (Fin 4) K),
      G = initialForm
          (scaledContactWeight (0 : Fin 4) scale bump)
          ((scale * m : ℕ) : ℤ) psi ∧
      d₀ ∈ G.support ∧
      3 ≤ ordinaryDegree4 d₀ ∧
      0 < scale ∧ 0 < bump ∧
      hessianDeterminant G = 0 ∧
      ¬ MvSupportOnFacet .qs G ∧
      HasBalancedMvSupport a b G ∧
      ∃ D : CrossFacetInitialData G
          (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4),
        ((∃ H : ToricFacet,
            AdjacentFacets .qs H ∧
              OnRay a b .qs H (toToricExponent D.facetExponent)) ∨
          ∃ e ∈ D.face.support,
            MvRankThreeOnFacet .pr e) := by
  rcases exists_singular_first_nonfacet_contact_with_boundary_vertices
      hm hdeg htop hout hlow hBal hMA with
    ⟨d₀, scale, bump, G, hG, hd₀G, hd₀deg, hscale, hbump,
      hzero, hnot, hGBal, _hboundary⟩

  have hsupports := firstContactCarrier_crossFacet_supports
    (F := .qs) (m := m) (scale := scale) (bump := bump)
    htop hattained hG hnot
  have hfacet : (zeroCoordinateSupport (0 : Fin 4) G).Nonempty := by
    simpa [facetOmittedCoordinate] using hsupports.1
  have houtside : (positiveCoordinateSupport (0 : Fin 4) G).Nonempty := by
    simpa [facetOmittedCoordinate] using hsupports.2.1
  have hcontact : ∀ d ∈ G.support,
      scaledContactExponentWeight (0 : Fin 4) scale bump d =
        ((scale * m : ℕ) : ℤ) := by
    simpa [facetOmittedCoordinate] using hsupports.2.2

  let D : CrossFacetInitialData G
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4) :=
    crossFacetInitialData hfacet houtside

  have hexit := D.qs_firstContact_endpoint_transition
    ha hb hcop hscale hbump hGBal hcontact hzero

  refine ⟨d₀, scale, bump, G, ?_, hd₀G, hd₀deg, hscale, hbump,
    hzero, hnot, hGBal, D, ?_⟩
  · simpa [facetOmittedCoordinate] using hG
  · rcases hexit.2 with hray | hpr
    · exact Or.inl hray
    · right
      let L := D.qsAffineLineData ha hb hscale hGBal hcontact
      have htopMem :
          L.exponent D.qsCoefficientPolynomial.natDegree ∈ D.face.support := by
        simpa [L] using
          (D.qsAffineLineData_top_mem_face_support
            ha hb hscale hGBal hcontact)
      refine ⟨L.exponent D.qsCoefficientPolynomial.natDegree, htopMem, ?_⟩
      simpa [L] using hpr

end

end HC4.Newton
