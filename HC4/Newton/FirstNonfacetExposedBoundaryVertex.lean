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

/-- Compact data extracted from the existential first-contact theorem.
Packaging the witness behind `Nonempty` keeps the later `Type`-valued
constructor from repeatedly normalising the long existential conjunction. -/
private structure FirstNonfacetContactCore
    (F : ToricFacet) (m : ℕ) (psi : MvPolynomial (Fin 4) K) where
  d0 : Fin 4 →₀ ℕ
  scale : ℕ
  bump : ℕ
  d0_degree_ge_three : 3 ≤ ordinaryDegree4 d0
  d0_omitted_pos : 0 < d0 (facetOmittedCoordinate F)
  scale_pos : 0 < scale
  hessian_zero :
    hessianDeterminant
      (initialForm
        (scaledContactWeight (facetOmittedCoordinate F) scale bump)
        (scale * m : ℕ) psi) = 0
  d0_mem_contact :
    d0 ∈
      (initialForm
        (scaledContactWeight (facetOmittedCoordinate F) scale bump)
        (scale * m : ℕ) psi).support

private theorem firstNonfacetContactCore_nonempty
    {F : ToricFacet} {m : ℕ}
    {psi : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m psi)
    (htop : TopDegreeOnFacet F m psi)
    (hout : HasNonlinearOutsideFacet F psi)
    (hlow : LowDegreeTameAtFacet F psi)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere psi) :
    Nonempty (FirstNonfacetContactCore (K := K) F m psi) := by
  rcases exists_singular_first_nonfacet_contact
      hm hdeg htop hout hlow hMA with
    ⟨d0, scale, bump, _hdPsi, hdDeg, hdPos,
      _hscaleEq, _hbumpEq, hscale, _hbump, _hbound,
      hzero, hdG, _hnotFacet⟩
  exact ⟨{
    d0 := d0
    scale := scale
    bump := bump
    d0_degree_ge_three := hdDeg
    d0_omitted_pos := hdPos
    scale_pos := hscale
    hessian_zero := hzero
    d0_mem_contact := hdG
  }⟩

/-- Compact data extracted from the finite-support exposed-vertex theorem. -/
private structure ExposedNonlinearBalancedCore (a b : ℕ) where
  carrier : MvPolynomial (Fin 4) K
  weight : Fin 4 → ℤ
  level : ℤ
  exponent : Fin 4 →₀ ℕ
  coeff : K
  hessian_zero : hessianDeterminant carrier = 0
  balanced : HasBalancedMvSupport a b carrier
  weight_bound : IsWeightLE weight level carrier
  exposed : initialForm weight level carrier = MvPolynomial.monomial exponent coeff
  coeff_ne_zero : coeff ≠ 0
  exponent_nonlinear : 3 ≤ ordinaryDegree4 exponent

private theorem exposedNonlinearBalancedCore_nonempty
    {a b : ℕ}
    {P : MvPolynomial (Fin 4) K}
    (hP : P ≠ 0)
    (hzero : hessianDeterminant P = 0)
    (hBal : HasBalancedMvSupport a b P)
    (hnonlinear : ∀ d ∈ P.support, 3 ≤ ordinaryDegree4 d) :
    Nonempty (ExposedNonlinearBalancedCore (K := K) a b) := by
  rcases exists_exposed_nonlinear_balanced_monomial
      hP hzero hBal hnonlinear with
    ⟨G, w, level, d, c, hGzero, hGBal, hwbound, hexposed, hc, hd3⟩
  exact ⟨{
    carrier := G
    weight := w
    level := level
    exponent := d
    coeff := c
    hessian_zero := hGzero
    balanced := hGBal
    weight_bound := hwbound
    exposed := hexposed
    coeff_ne_zero := hc
    exponent_nonlinear := hd3
  }⟩

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
  let C : FirstNonfacetContactCore (K := K) F m psi :=
    Classical.choice
      (firstNonfacetContactCore_nonempty hm hdeg htop hout hlow hMA)

  let j := facetOmittedCoordinate F
  let G := initialForm (scaledContactWeight j C.scale C.bump)
    (C.scale * m : ℕ) psi

  have hdWeight :
      scaledContactExponentWeight j C.scale C.bump C.d0 =
        (C.scale * m : ℕ) := by
    have hw :=
      (initialForm_isWeightedHomogeneous
        (scaledContactWeight j C.scale C.bump) (C.scale * m : ℕ) psi)
        (MvPolynomial.mem_support_iff.mp C.d0_mem_contact)
    rw [weight_scaledContactWeight] at hw
    exact hw

  have hbumpBound : C.bump ≤ C.scale * (m - 3) :=
    bump_le_scale_mul_m_sub_three C.scale_pos
      (by simpa [j] using C.d0_omitted_pos)
      C.d0_degree_ge_three hdWeight

  have hlow' :
      ∀ d ∈ psi.support, ordinaryDegree4 d < 3 → d j ≤ 1 := by
    simpa [LowDegreeTameAtFacet, j] using hlow

  have hGnonlinear : ∀ d ∈ G.support, 3 ≤ ordinaryDegree4 d := by
    dsimp [G]
    exact firstContact_initialForm_support_degree_ge_three
      hm C.scale_pos hbumpBound hlow'

  have hGzero : hessianDeterminant G = 0 := by
    simpa [G, j] using C.hessian_zero
  have hGBal : HasBalancedMvSupport a b G := by
    dsimp [G]
    exact hBal.initialForm
      (scaledContactWeight j C.scale C.bump) (C.scale * m : ℕ)
  have hGne : G ≠ 0 := by
    exact MvPolynomial.support_nonempty.mp
      ⟨C.d0, by simpa [G, j] using C.d0_mem_contact⟩

  let V : ExposedNonlinearBalancedCore (K := K) a b :=
    Classical.choice
      (exposedNonlinearBalancedCore_nonempty hGne hGzero hGBal hGnonlinear)

  have hstratum := exposed_balanced_monomial_rankThree_or_extremeRay
    ha hb hcop V.balanced V.weight_bound V.hessian_zero
      V.exposed V.coeff_ne_zero V.exponent_nonlinear

  exact {
    carrier := V.carrier
    weight := V.weight
    level := V.level
    exponent := V.exponent
    coeff := V.coeff
    carrier_hessian_zero := V.hessian_zero
    carrier_balanced := V.balanced
    weight_bound := V.weight_bound
    exposed := V.exposed
    coeff_ne_zero := V.coeff_ne_zero
    exponent_nonlinear := V.exponent_nonlinear
    stratum := hstratum
  }

end

end HC4.Newton
