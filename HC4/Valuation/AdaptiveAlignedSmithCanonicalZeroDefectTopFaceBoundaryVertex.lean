import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTopFaceHomogeneous
import HC4.Newton.FirstNonfacetExposedBoundaryVertex
import Mathlib.Tactic

/-!
# A18.5.81: expose an actual toric boundary vertex of the zero-defect top face

A18.5.12 selects a genuine nonzero nonlinear Hessian-singular maximal ordinary
face at raw defect zero.  A18.5.78/80 exposes its homogeneity and preserves any
certified symmetric torus grading carried by the source special fibre.

The finite-support Newton machinery can now be applied directly to that actual
face.  Successive coordinate maxima expose a nonzero nonlinear singleton while
preserving singularity and balance, and the existing boundary-stratum theorem
classifies its exponent as either rank three on a toric facet or an extreme
transition ray.

This is only a provenance adapter: no toric grading is manufactured and no
Hessian/Schur rank label is reinterpreted as an exponent-line statement.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData

/-- Proposition-valued wrapper for the finite-support exposure theorem.  The
existential theorem may be destructured here because the target is `Nonempty`;
the public `Type`-valued constructor then performs only one classical choice. -/
private theorem exposedBoundaryVertex_nonempty
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData s)
    {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hBal : HasBalancedMvSupport a b
      (polynomialFamilySpecialFiber s.family)) :
    Nonempty (FirstNonfacetExposedBoundaryVertexData (K := K) a b) := by
  have hFaceBal : HasBalancedMvSupport a b D.face :=
    D.face_balanced_of_specialFiber_balanced hBal

  rcases exists_exposed_nonlinear_balanced_monomial
      D.face_ne_zero D.hessian_zero hFaceBal
      D.face_support_degree_ge_three with
    ⟨G, w, level, d, c, hGzero, hGBal, hwbound, hexposed, hc, hd3⟩

  have hstratum := exposed_balanced_monomial_rankThree_or_extremeRay
    ha hb hcop hGBal hwbound hGzero hexposed hc hd3

  exact ⟨{
    carrier := G
    weight := w
    level := level
    exponent := d
    coeff := c
    carrier_hessian_zero := hGzero
    carrier_balanced := hGBal
    weight_bound := hwbound
    exposed := hexposed
    coeff_ne_zero := hc
    exponent_nonlinear := hd3
    stratum := hstratum
  }⟩

/-- **A18.5.81 — actual classified boundary vertex of the zero-defect carrier.**

Once the source special fibre carries a positive primitive symmetric torus
grading, the selected zero-defect singular top face has an actually exposed
nonlinear boundary monomial.  The returned record retains the singular carrier,
its balance certificate, the exact singleton exposure, and the rank-three versus
extreme-ray toric stratum of that genuine exponent. -/
noncomputable def exposedBoundaryVertex
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData s)
    {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    (hBal : HasBalancedMvSupport a b
      (polynomialFamilySpecialFiber s.family)) :
    FirstNonfacetExposedBoundaryVertexData (K := K) a b :=
  Classical.choice (exposedBoundaryVertex_nonempty D ha hb hcop hBal)

end AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData

end

end HC4.Valuation
