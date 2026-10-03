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

open HC4.Polynomial
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

/-- Coordinate form of the surviving `.qs` extreme-ray endpoint.  This is
the exact sparse endpoint shape consumed by the next complementary-line
adapter. -/
theorem CrossFacetInitialData.qs_extremeRay_facet_coordinates
    {K : Type*} [Field K] [CharZero K]
    {F : MvPolynomial (Fin 4) K}
    {a b : ℕ}
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    {H : ToricFacet}
    (hAdj : AdjacentFacets .qs H)
    (hRay : OnRay a b .qs H (toToricExponent D.facetExponent)) :
    (∃ n : ℕ,
        D.facetExponent 0 = 0 ∧
        D.facetExponent 1 = n ∧
        D.facetExponent 2 = n ∧
        D.facetExponent 3 = 0) ∨
      (∃ n : ℕ,
        D.facetExponent 0 = 0 ∧
        D.facetExponent 1 = a * n ∧
        D.facetExponent 2 = 0 ∧
        D.facetExponent 3 = b * n) := by
  rcases D.qs_extremeRay_facet_normalForm hAdj hRay with hq | hs
  · rcases hq with ⟨n, hn⟩
    left
    refine ⟨n, ?_, ?_, ?_, ?_⟩
    · exact D.facet_coordinate_zero
    · have h := congrArg (fun u : Exponent => u.x2) hn
      simpa [Exponent.scale, qExponent] using h
    · have h := congrArg (fun u : Exponent => u.x3) hn
      simpa [Exponent.scale, qExponent] using h
    · have h := congrArg (fun u : Exponent => u.x4) hn
      simpa [Exponent.scale, qExponent] using h
  · rcases hs with ⟨n, hn⟩
    right
    refine ⟨n, ?_, ?_, ?_, ?_⟩
    · exact D.facet_coordinate_zero
    · have h := congrArg (fun u : Exponent => u.x2) hn
      simpa [Exponent.scale, sExponent, Nat.mul_comm] using h
    · have h := congrArg (fun u : Exponent => u.x3) hn
      simpa [Exponent.scale, sExponent] using h
    · have h := congrArg (fun u : Exponent => u.x4) hn
      simpa [Exponent.scale, sExponent, Nat.mul_comm] using h


/-- A nonlinear surviving extreme-ray endpoint is a positive multiple of the
corresponding ray generator; the origin case is excluded by ordinary degree. -/
theorem CrossFacetInitialData.qs_extremeRay_facet_coordinates_pos
    {K : Type*} [Field K] [CharZero K]
    {F : MvPolynomial (Fin 4) K}
    {a b : ℕ}
    (D : CrossFacetInitialData F
      (crossFacetOppositeCoordinate (0 : Fin 4)) (0 : Fin 4))
    {H : ToricFacet}
    (hAdj : AdjacentFacets .qs H)
    (hRay : OnRay a b .qs H (toToricExponent D.facetExponent))
    (hdeg : 3 ≤ ordinaryDegree4 D.facetExponent) :
    (∃ n : ℕ, 0 < n ∧
        D.facetExponent 0 = 0 ∧
        D.facetExponent 1 = n ∧
        D.facetExponent 2 = n ∧
        D.facetExponent 3 = 0) ∨
      (∃ n : ℕ, 0 < n ∧
        D.facetExponent 0 = 0 ∧
        D.facetExponent 1 = a * n ∧
        D.facetExponent 2 = 0 ∧
        D.facetExponent 3 = b * n) := by
  rcases D.qs_extremeRay_facet_coordinates hAdj hRay with hq | hs
  · rcases hq with ⟨n, h0, h1, h2, h3⟩
    left
    refine ⟨n, ?_, h0, h1, h2, h3⟩
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [ordinaryDegree4, h0, h1, h2, h3, hn0] at hdeg
  · rcases hs with ⟨n, h0, h1, h2, h3⟩
    right
    refine ⟨n, ?_, h0, h1, h2, h3⟩
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [ordinaryDegree4, h0, h1, h2, h3, hn0] at hdeg

end

end HC4.Newton
