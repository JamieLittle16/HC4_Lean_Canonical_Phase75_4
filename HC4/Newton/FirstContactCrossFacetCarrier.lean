import HC4.Newton.FirstNonfacetBoundary
import HC4.Newton.FiniteSupportCrossFacetExposure
import Mathlib.Tactic

/-!
# A18.5.70: first-contact carrier really crosses the starting facet

The first non-facet contact theorem retains an outside supported exponent and
proves that its exact initial form is not confined to the starting toric facet.
To apply the finite cross-facet exposure we also need an *actual* supported
exponent on that facet.

`TopDegreeOnFacet` alone is only a universal statement and does not assert that
the top degree is attained.  This file therefore keeps attainment explicit.
An attained degree-`m` exponent lies on the starting facet, has exact cleared
contact weight `scale * m`, and hence survives in the first-contact initial
form.  Non-confinement supplies a supported exponent with positive omitted
coordinate.  Thus both finite support slices used by A18.5.65c are genuinely
nonempty.

The final theorem also records the exact contact equation on every exponent of
the carrier.  No support point is invented and no vacuous top-degree premise is
used as an existence statement.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Every supported exponent of an exact scaled-contact initial form lies on
the exact cleared contact level. -/
theorem scaledContactInitialForm_support_contact_eq
    {j : Fin 4} {scale bump m : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (initialForm
      (scaledContactWeight j scale bump)
      ((scale * m : ℕ) : ℤ) psi).support) :
    scaledContactExponentWeight j scale bump d =
      ((scale * m : ℕ) : ℤ) := by
  have hne :
      MvPolynomial.coeff d
        (initialForm
          (scaledContactWeight j scale bump)
          ((scale * m : ℕ) : ℤ) psi) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  rw [coeff_initialForm] at hne
  split_ifs at hne with hw
  · rw [weight_scaledContactWeight] at hw
    exact hw
  · exact (hne rfl).elim

/-- An actually attained top-degree exponent survives in the scaled first
contact and supplies the zero-coordinate side of the cross-facet carrier. -/
theorem zeroCoordinateSupport_nonempty_of_topDegree_attained
    {F : ToricFacet} {m scale bump : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    (htop : TopDegreeOnFacet F m psi)
    (hattained : ∃ v ∈ psi.support, ordinaryDegree4 v = m) :
    (zeroCoordinateSupport (facetOmittedCoordinate F)
      (initialForm
        (scaledContactWeight (facetOmittedCoordinate F) scale bump)
        ((scale * m : ℕ) : ℤ) psi)).Nonempty := by
  rcases hattained with ⟨v, hv, hvdeg⟩
  have hvzero : v (facetOmittedCoordinate F) = 0 :=
    topDegree_omittedCoordinate_zero htop v hv hvdeg
  have hvcontact :
      scaledContactExponentWeight (facetOmittedCoordinate F) scale bump v =
        ((scale * m : ℕ) : ℤ) := by
    simpa using scaledContact_top_facet
      (j := facetOmittedCoordinate F) (scale := scale) (bump := bump)
      hvzero hvdeg
  have hvweight :
      Finsupp.weight
          (scaledContactWeight (facetOmittedCoordinate F) scale bump) v =
        ((scale * m : ℕ) : ℤ) := by
    rw [weight_scaledContactWeight]
    exact hvcontact
  have hvinit :
      v ∈ (initialForm
        (scaledContactWeight (facetOmittedCoordinate F) scale bump)
        ((scale * m : ℕ) : ℤ) psi).support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [coeff_initialForm]
    simp [hvweight, MvPolynomial.mem_support_iff.mp hv]
  exact ⟨v, mem_zeroCoordinateSupport.mpr ⟨hvinit, hvzero⟩⟩

/-- Failure of confinement to a toric facet supplies an actual supported
exponent with positive omitted coordinate. -/
theorem positiveCoordinateSupport_nonempty_of_not_supportOnFacet
    {F : ToricFacet} {G : MvPolynomial (Fin 4) K}
    (hnot : ¬ MvSupportOnFacet F G) :
    (positiveCoordinateSupport (facetOmittedCoordinate F) G).Nonempty := by
  classical
  have hfail :
      ¬ ∀ d : Fin 4 →₀ ℕ, d ∈ G.support →
        OnFacet F (toToricExponent d) := by
    intro hall
    exact hnot hall
  push_neg at hfail
  rcases hfail with ⟨d, hd, hnotd⟩
  have hdne : d (facetOmittedCoordinate F) ≠ 0 := by
    intro hz
    exact hnotd ((onFacet_toToricExponent_iff F d).2 hz)
  have hdpos : 0 < d (facetOmittedCoordinate F) := Nat.pos_of_ne_zero hdne
  exact ⟨d, mem_positiveCoordinateSupport.mpr ⟨hd, hdpos⟩⟩

/-- **A18.5.70 first-contact cross-facet provenance.**

If the declared top nonlinear degree is genuinely attained, then the exact
first-contact carrier has both a supported exponent on the starting coordinate
facet and a supported exponent strictly outside it.  Every supported exponent
also retains the exact cleared contact equation required by the affine-line
recogniser. -/
theorem firstContactCarrier_crossFacet_supports
    {F : ToricFacet} {m scale bump : ℕ}
    {psi G : MvPolynomial (Fin 4) K}
    (htop : TopDegreeOnFacet F m psi)
    (hattained : ∃ v ∈ psi.support, ordinaryDegree4 v = m)
    (hG : G = initialForm
      (scaledContactWeight (facetOmittedCoordinate F) scale bump)
      ((scale * m : ℕ) : ℤ) psi)
    (hnot : ¬ MvSupportOnFacet F G) :
    (zeroCoordinateSupport (facetOmittedCoordinate F) G).Nonempty ∧
      (positiveCoordinateSupport (facetOmittedCoordinate F) G).Nonempty ∧
      ∀ d ∈ G.support,
        scaledContactExponentWeight (facetOmittedCoordinate F) scale bump d =
          ((scale * m : ℕ) : ℤ) := by
  subst G
  refine ⟨zeroCoordinateSupport_nonempty_of_topDegree_attained
      (scale := scale) (bump := bump) htop hattained,
    positiveCoordinateSupport_nonempty_of_not_supportOnFacet hnot, ?_⟩
  intro d hd
  exact scaledContactInitialForm_support_contact_eq hd

end

end HC4.Newton
