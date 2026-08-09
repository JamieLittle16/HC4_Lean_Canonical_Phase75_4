import HC4.Newton.FirstContactSelection

/-!
# The genuine first non-facet nonlinear contact

This is the finite-support part of Proposition 6.2 in the manuscript.  Starting
from a highest nonlinear degree `m` whose degree-`m` support lies in a chosen
toric facet, and assuming there is nonlinear support outside that facet, we
construct the manuscript's first-contact weight from the support itself.

The resulting exact initial polynomial has zero Hessian determinant and is
not confined to the original facet.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

/-- Nonlinear support is bounded by `m`. -/
def NonlinearDegreeBound {K : Type*} [CommSemiring K]
    (m : ℕ) (p : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ p.support, 3 ≤ ordinaryDegree4 d → ordinaryDegree4 d ≤ m

/-- The degree-`m` nonlinear support lies in the chosen toric facet. -/
def TopDegreeOnFacet {K : Type*} [CommSemiring K]
    (F : ToricFacet) (m : ℕ) (p : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ p.support, ordinaryDegree4 d = m → OnFacet F (toToricExponent d)

/-- There is a genuinely nonlinear supported monomial outside the facet. -/
def HasNonlinearOutsideFacet {K : Type*} [CommSemiring K]
    (F : ToricFacet) (p : MvPolynomial (Fin 4) K) : Prop :=
  ∃ d ∈ p.support, 3 ≤ ordinaryDegree4 d ∧ ¬ OnFacet F (toToricExponent d)

/-- The fixed low-degree part is tame in the omitted coordinate.  For the HC4
normalisation `p+q`, every quadratic monomial has each coordinate exponent at
most one, which is exactly this condition. -/
def LowDegreeTameAtFacet {K : Type*} [CommSemiring K]
    (F : ToricFacet) (p : MvPolynomial (Fin 4) K) : Prop :=
  ∀ d ∈ p.support, ordinaryDegree4 d < 3 → d (facetOmittedCoordinate F) ≤ 1

/-- Outside nonlinear support for a toric facet is nonempty exactly when there
is a nonlinear supported exponent outside that facet. -/
theorem nonlinearOutsideSupport_nonempty_of_hasNonlinearOutsideFacet
    {K : Type*} [CommSemiring K]
    {F : ToricFacet} {p : MvPolynomial (Fin 4) K}
    (hout : HasNonlinearOutsideFacet F p) :
    (nonlinearOutsideSupport (facetOmittedCoordinate F) p).Nonempty := by
  rcases hout with ⟨d, hd, hdeg, hnot⟩
  refine ⟨d, mem_nonlinearOutsideSupport.mpr ⟨hd, hdeg, ?_⟩⟩
  have hne : d (facetOmittedCoordinate F) ≠ 0 := by
    intro hz
    apply hnot
    exact (onFacet_toToricExponent_iff F d).2 hz
  exact Nat.pos_of_ne_zero hne

/-- The top-facet hypothesis translated to the omitted coordinate. -/
theorem topDegree_omittedCoordinate_zero
    {K : Type*} [CommSemiring K]
    {F : ToricFacet} {m : ℕ} {p : MvPolynomial (Fin 4) K}
    (htop : TopDegreeOnFacet F m p) :
    ∀ d ∈ p.support, ordinaryDegree4 d = m →
      d (facetOmittedCoordinate F) = 0 := by
  intro d hd hdeg
  exact (onFacet_toToricExponent_iff F d).1 (htop d hd hdeg)

/-- **Constructed first non-facet contact.**

The support itself supplies positive integers `scale,bump`, and the exact
initial polynomial at weight

`scale*(1,1,1,1) + bump*e_j`

has zero Hessian determinant while still containing a monomial outside the
chosen toric facet. -/
theorem exists_singular_first_nonfacet_contact
    {K : Type*} [CommRing K] [Nontrivial K]
    {F : ToricFacet} {m : ℕ} {ψ : MvPolynomial (Fin 4) K}
    (hm : 3 ≤ m)
    (hdeg : NonlinearDegreeBound m ψ)
    (htop : TopDegreeOnFacet F m ψ)
    (hout : HasNonlinearOutsideFacet F ψ)
    (hlow : LowDegreeTameAtFacet F ψ)
    (hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere ψ) :
    ∃ (d₀ : Fin 4 →₀ ℕ) (scale bump : ℕ),
      d₀ ∈ ψ.support ∧ 3 ≤ ordinaryDegree4 d₀ ∧
      0 < d₀ (facetOmittedCoordinate F) ∧
      scale = d₀ (facetOmittedCoordinate F) ∧
      bump = m - ordinaryDegree4 d₀ ∧
      0 < scale ∧ 0 < bump ∧
      HC4.Polynomial.IsWeightLE
        (scaledContactWeight (facetOmittedCoordinate F) scale bump)
        (scale * m : ℕ) ψ ∧
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.initialForm
          (scaledContactWeight (facetOmittedCoordinate F) scale bump)
          (scale * m : ℕ) ψ) = 0 ∧
      d₀ ∈ (HC4.Polynomial.initialForm
          (scaledContactWeight (facetOmittedCoordinate F) scale bump)
          (scale * m : ℕ) ψ).support ∧
      ¬ MvSupportOnFacet F
        (HC4.Polynomial.initialForm
          (scaledContactWeight (facetOmittedCoordinate F) scale bump)
          (scale * m : ℕ) ψ) := by
  let j := facetOmittedCoordinate F
  have hout' : (nonlinearOutsideSupport j ψ).Nonempty := by
    simpa [j] using nonlinearOutsideSupport_nonempty_of_hasNonlinearOutsideFacet hout
  have hdeg' : ∀ d ∈ ψ.support, 3 ≤ ordinaryDegree4 d → ordinaryDegree4 d ≤ m := by
    simpa [NonlinearDegreeBound] using hdeg
  have htop' : ∀ d ∈ ψ.support, ordinaryDegree4 d = m → d j = 0 := by
    simpa [j] using topDegree_omittedCoordinate_zero htop
  have hlow' : ∀ d ∈ ψ.support, ordinaryDegree4 d < 3 → d j ≤ 1 := by
    simpa [LowDegreeTameAtFacet, j] using hlow
  rcases exists_minimal_contactExponent (m := m) hout' with ⟨d₀, hd₀, hmin⟩
  let scale := d₀ j
  let bump := m - ordinaryDegree4 d₀
  have hlevel := selected_contact_level hd₀ hdeg' htop'
  dsimp only at hlevel
  have hscale : 0 < scale := by simpa [scale] using hlevel.1
  have hbump : 0 < bump := by simpa [bump] using hlevel.2.1
  have hcontact₀ : scaledContactExponentWeight j scale bump d₀ = (scale * m : ℕ) := by
    simpa [scale, bump] using hlevel.2.2
  have hbound : HC4.Polynomial.IsWeightLE
      (scaledContactWeight j scale bump) (scale * m : ℕ) ψ := by
    simpa [scale, bump] using
      selected_contact_isWeightLE hm hd₀ hmin hdeg' htop' hlow'
  have hbumpBound : bump ≤ scale * (m - 3) := by
    exact bump_le_scale_mul_m_sub_three hscale
      (mem_nonlinearOutsideSupport.mp hd₀).2.2
      (mem_nonlinearOutsideSupport.mp hd₀).2.1 hcontact₀
  have hcontactBound : bump + 3 * scale ≤ scale * m := by
    calc
      bump + 3 * scale ≤ scale * (m - 3) + 3 * scale :=
        Nat.add_le_add_right hbumpBound _
      _ = scale * ((m - 3) + 3) := by ring
      _ = scale * m := by rw [Nat.sub_add_cancel hm]
  have hdet : HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm (scaledContactWeight j scale bump)
        (scale * m : ℕ) ψ) = 0 :=
    scaledContact_hessianDeterminant_eq_zero_of_isWeightLE
      hscale hcontactBound hbound hMA
  have hd₀supp : d₀ ∈ ψ.support := (mem_nonlinearOutsideSupport.mp hd₀).1
  have hd₀nonlin : 3 ≤ ordinaryDegree4 d₀ :=
    (mem_nonlinearOutsideSupport.mp hd₀).2.1
  have hd₀j : 0 < d₀ j := (mem_nonlinearOutsideSupport.mp hd₀).2.2
  have hd₀weight :
      Finsupp.weight (scaledContactWeight j scale bump) d₀ = (scale * m : ℕ) := by
    rw [weight_scaledContactWeight]
    exact hcontact₀
  have hd₀init : d₀ ∈ (HC4.Polynomial.initialForm
      (scaledContactWeight j scale bump) (scale * m : ℕ) ψ).support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [HC4.Polynomial.coeff_initialForm]
    simp [hd₀weight, MvPolynomial.mem_support_iff.mp hd₀supp]
  have hnotFacet : ¬ MvSupportOnFacet F
      (HC4.Polynomial.initialForm
        (scaledContactWeight j scale bump) (scale * m : ℕ) ψ) := by
    intro hFacet
    have hz := (onFacet_toToricExponent_iff F d₀).1 (hFacet d₀ hd₀init)
    change d₀ j = 0 at hz
    omega
  refine ⟨d₀, scale, bump, hd₀supp, hd₀nonlin, ?_, rfl, rfl,
    hscale, hbump, hbound, hdet, hd₀init, hnotFacet⟩
  simpa [j] using hd₀j

end

end HC4.Newton
