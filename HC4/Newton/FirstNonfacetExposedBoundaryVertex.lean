import HC4.Newton.FirstNonfacetBoundary
import HC4.Newton.FirstContactNonlinearSupport
import HC4.Newton.FiniteSupportExposedVertex
import Mathlib.Tactic

/-!
# A18.5.34: the first non-facet contact has an actual classified boundary vertex

Phase 56 constructs the singular balanced first-contact polynomial.  A18.5.32
proves that its complete support is nonlinear, and A18.5.33 constructively
exposes a singleton monomial by four successive coordinate maxima.

The existing A18.5.20 boundary-stratum theorem can therefore be invoked on an
*actual* exposed monomial, not on a hypothetical future exposure.  The output
is the finite dichotomy required by the Newton endgame: rank three in the
relative interior of one toric facet, or an extreme transition ray.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Full provenance for one actually exposed nonlinear boundary vertex of the
first non-facet contact. -/
structure FirstNonfacetExposedBoundaryVertexData
    (a b : ℕ) where
  carrier : MvPolynomial (Fin 4) K
  weight : Fin 4 → ℤ
  level : ℤ
  exponent : Fin 4 →₀ ℕ
  coeff : K
  carrier_hessian_zero : hessianDeterminant carrier = 0
  carrier_balanced : HasBalancedMvSupport a b carrier
  weight_bound : IsWeightLE weight level carrier
  exposed : initialForm weight level carrier = MvPolynomial.monomial exponent coeff
  coeff_ne_zero : coeff ≠ 0
  exponent_nonlinear : 3 ≤ ordinaryDegree4 exponent
  stratum :
    (∃ facet : ToricFacet, MvRankThreeOnFacet facet exponent) ∨
      (∃ facet next : ToricFacet,
        AdjacentFacets facet next ∧
          OnRay a b facet next (toToricExponent exponent))

/-- **Constructed and classified boundary vertex of the genuine first
non-facet contact.** -/
noncomputable def firstNonfacetExposedBoundaryVertex
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {F : ToricFacet} {m : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m psi)
    (htop : TopDegreeOnFacet F m psi)
    (hout : HasNonlinearOutsideFacet F psi)
    (hlow : LowDegreeTameAtFacet F psi)
    (hBal : HasBalancedMvSupport a b psi)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere psi) :
    FirstNonfacetExposedBoundaryVertexData (K := K) a b := by
  have hcontact :=
    exists_singular_first_nonfacet_contact hm hdeg htop hout hlow hMA
  let d0 := Classical.choose hcontact
  have hcontact1 := Classical.choose_spec hcontact
  let scale := Classical.choose hcontact1
  have hcontact2 := Classical.choose_spec hcontact1
  let bump := Classical.choose hcontact2
  have hs := Classical.choose_spec hcontact2
  have hdPsi := hs.1
  have hs := hs.2
  have hdDeg := hs.1
  have hs := hs.2
  have hdPos := hs.1
  have hs := hs.2
  have hscaleEq := hs.1
  have hs := hs.2
  have hbumpEq := hs.1
  have hs := hs.2
  have hscale := hs.1
  have hs := hs.2
  have hbump := hs.1
  have hs := hs.2
  have hbound := hs.1
  have hs := hs.2
  have hzero := hs.1
  have hs := hs.2
  have hdG := hs.1
  have hnotFacet := hs.2

  let j := facetOmittedCoordinate F
  let G := initialForm (scaledContactWeight j scale bump)
    (scale * m : ℕ) psi

  have hdWeight :
      scaledContactExponentWeight j scale bump d0 = (scale * m : ℕ) := by
    have hw :=
      (initialForm_isWeightedHomogeneous
        (scaledContactWeight j scale bump) (scale * m : ℕ) psi)
        (MvPolynomial.mem_support_iff.mp hdG)
    rw [weight_scaledContactWeight] at hw
    exact hw

  have hbumpBound : bump ≤ scale * (m - 3) :=
    bump_le_scale_mul_m_sub_three hscale
      (by simpa [j] using hdPos) hdDeg hdWeight

  have hlow' :
      ∀ d ∈ psi.support, ordinaryDegree4 d < 3 → d j ≤ 1 := by
    simpa [LowDegreeTameAtFacet, j] using hlow

  have hGnonlinear : ∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d := by
    dsimp [G]
    exact firstContact_initialForm_support_degree_ge_three
      hm hscale hbumpBound hlow'

  have hGzero : hessianDeterminant G = 0 := by
    simpa [G, j] using hzero
  have hGBal : HasBalancedMvSupport a b G := by
    dsimp [G]
    exact hBal.initialForm (scaledContactWeight j scale bump) (scale * m : ℕ)
  have hGne : G ≠ 0 := by
    exact MvPolynomial.support_nonempty.mp ⟨d0, by simpa [G, j] using hdG⟩

  have hexposed :=
    exists_exposed_nonlinear_balanced_monomial
      hGne hGzero hGBal hGnonlinear
  let H := Classical.choose hexposed
  have hexposed1 := Classical.choose_spec hexposed
  let w := Classical.choose hexposed1
  have hexposed2 := Classical.choose_spec hexposed1
  let level := Classical.choose hexposed2
  have hexposed3 := Classical.choose_spec hexposed2
  let d := Classical.choose hexposed3
  have hexposed4 := Classical.choose_spec hexposed3
  let c := Classical.choose hexposed4
  have hs := Classical.choose_spec hexposed4
  have hHzero := hs.1
  have hs := hs.2
  have hHBal := hs.1
  have hs := hs.2
  have hwbound := hs.1
  have hs := hs.2
  have hexposedEq := hs.1
  have hs := hs.2
  have hc := hs.1
  have hd3 := hs.2

  have hstratum := exposed_balanced_monomial_rankThree_or_extremeRay
    ha hb hcop hHBal hwbound hHzero hexposedEq hc hd3

  exact {
    carrier := H
    weight := w
    level := level
    exponent := d
    coeff := c
    carrier_hessian_zero := hHzero
    carrier_balanced := hHBal
    weight_bound := hwbound
    exposed := hexposedEq
    coeff_ne_zero := hc
    exponent_nonlinear := hd3
    stratum := hstratum
  }

end

end HC4.Newton
