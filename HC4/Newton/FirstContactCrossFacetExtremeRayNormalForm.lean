import HC4.Newton.FirstContactCrossFacetExit
import Mathlib.Tactic

/-!
# Normal form of the surviving canonical first-contact extreme ray

The genuine `.qs` first-contact exit has already eliminated the affine
rank-three alternative.  Its selected facet endpoint therefore lies on an
adjacent toric extreme ray.  There are only two such rays adjacent to
`.qs`: the `q` ray through `.rq`, and the `s` ray through `.sp`.

This file records that finite normalization explicitly.  It is the first
adapter needed to turn the surviving first-contact exit into the existing
complementary-edge polynomial obstruction.
-/

namespace HC4.Newton

open HC4.Toric

noncomputable section

/-- An adjacent ray out of `.qs` is literally either the `q` ray or the
`s` ray.  The opposite `.pr` facet and `.qs` itself are excluded by
adjacency. -/
theorem qs_adjacent_onRay_normalForm
    {a b : ℕ}
    {H : ToricFacet}
    {u : Exponent}
    (hAdj : AdjacentFacets .qs H)
    (hRay : OnRay a b .qs H u) :
    (∃ n : ℕ, u = Exponent.scale n qExponent) ∨
      (∃ n : ℕ, u = Exponent.scale n (sExponent a b)) := by
  cases H with
  | pr =>
      exfalso
      exact hAdj.2 (by simp [OppositeFacets])
  | rq =>
      left
      simpa [OnRay] using hRay
  | qs =>
      exact (hAdj.1 rfl).elim
  | sp =>
      right
      simpa [OnRay] using hRay

/-- Cross-facet form used by the E-stage: the actual selected `.qs` facet
exponent of the first-contact face has one of the two explicit extreme-ray
normal forms. -/
theorem CrossFacetInitialData.qs_extremeRay_facet_normalForm
    {K : Type*} [Field K] [CharZero K]
    {F : MvPolynomial (Fin 4) K}
    {a b : ℕ}
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    {H : ToricFacet}
    (hAdj : AdjacentFacets .qs H)
    (hRay : OnRay a b .qs H (toToricExponent D.facetExponent)) :
    (∃ n : ℕ,
        toToricExponent D.facetExponent =
          Exponent.scale n qExponent) ∨
      (∃ n : ℕ,
        toToricExponent D.facetExponent =
          Exponent.scale n (sExponent a b)) :=
  qs_adjacent_onRay_normalForm hAdj hRay

end

end HC4.Newton
