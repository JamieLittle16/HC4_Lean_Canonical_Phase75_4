import HC4.Newton.FiniteSupportSingularBoundaryVertex
import HC4.Newton.MvBoundaryStrata
import Mathlib.Tactic

/-!
# A18.5.93: balance-free boundary rank split

A18.5.92 produces a genuine coordinate-boundary exponent from every exposed
singular nonlinear carrier without assuming a torus grading.  In four
variables there is then an elementary exhaustive split:

* exactly one coordinate vanishes, so the exponent is rank three in the
  relative interior of the corresponding coordinate facet;
* at least two distinct coordinates vanish, so the exponent is already on a
  codimension-two coordinate boundary.

This is purely a statement about nonnegative exponents.  No balance relation
is used.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric

/-- A four-variable exponent lies on a codimension-two coordinate boundary
when two distinct coordinates vanish. -/
def MvExponentOnCodimensionTwoBoundary (d : Fin 4 →₀ ℕ) : Prop :=
  ∃ i j : Fin 4, i ≠ j ∧ d i = 0 ∧ d j = 0

/-- **Balance-free coordinate-boundary rank split.** -/
theorem mvBoundary_rankThreeFacet_or_codimensionTwo
    {d : Fin 4 →₀ ℕ}
    (hbdry : MvExponentOnBoundary d) :
    (∃ F : ToricFacet, MvRankThreeOnFacet F d) ∨
      MvExponentOnCodimensionTwoBoundary d := by
  rw [mvExponentOnBoundary_iff_coordinate_zero] at hbdry
  rcases hbdry with h0 | h1 | h2 | h3
  · by_cases h1z : d 1 = 0
    · right
      exact ⟨0, 1, by decide, h0, h1z⟩
    · by_cases h2z : d 2 = 0
      · right
        exact ⟨0, 2, by decide, h0, h2z⟩
      · by_cases h3z : d 3 = 0
        · right
          exact ⟨0, 3, by decide, h0, h3z⟩
        · left
          refine ⟨.qs, ?_⟩
          exact ⟨h0,
            Nat.pos_of_ne_zero h1z,
            Nat.pos_of_ne_zero h2z,
            Nat.pos_of_ne_zero h3z⟩
  · by_cases h0z : d 0 = 0
    · right
      exact ⟨1, 0, by decide, h1, h0z⟩
    · by_cases h2z : d 2 = 0
      · right
        exact ⟨1, 2, by decide, h1, h2z⟩
      · by_cases h3z : d 3 = 0
        · right
          exact ⟨1, 3, by decide, h1, h3z⟩
        · left
          refine ⟨.pr, ?_⟩
          exact ⟨h1,
            Nat.pos_of_ne_zero h0z,
            Nat.pos_of_ne_zero h2z,
            Nat.pos_of_ne_zero h3z⟩
  · by_cases h0z : d 0 = 0
    · right
      exact ⟨2, 0, by decide, h2, h0z⟩
    · by_cases h1z : d 1 = 0
      · right
        exact ⟨2, 1, by decide, h2, h1z⟩
      · by_cases h3z : d 3 = 0
        · right
          exact ⟨2, 3, by decide, h2, h3z⟩
        · left
          refine ⟨.sp, ?_⟩
          exact ⟨h2,
            Nat.pos_of_ne_zero h0z,
            Nat.pos_of_ne_zero h1z,
            Nat.pos_of_ne_zero h3z⟩
  · by_cases h0z : d 0 = 0
    · right
      exact ⟨3, 0, by decide, h3, h0z⟩
    · by_cases h1z : d 1 = 0
      · right
        exact ⟨3, 1, by decide, h3, h1z⟩
      · by_cases h2z : d 2 = 0
        · right
          exact ⟨3, 2, by decide, h3, h2z⟩
        · left
          refine ⟨.rq, ?_⟩
          exact ⟨h3,
            Nat.pos_of_ne_zero h0z,
            Nat.pos_of_ne_zero h1z,
            Nat.pos_of_ne_zero h2z⟩

/-- The exposed singular vertex from A18.5.92 therefore has the exact
rank-three-facet versus codimension-two split needed by terminal assembly. -/
theorem ExposedSingularNonlinearBoundaryVertexData.rankThreeFacet_or_codimensionTwo
    {K : Type*} [Field K] [CharZero K]
    {F : MvPolynomial (Fin 4) K}
    (D : ExposedSingularNonlinearBoundaryVertexData F) :
    (∃ facet : ToricFacet, MvRankThreeOnFacet facet D.exponent) ∨
      MvExponentOnCodimensionTwoBoundary D.exponent :=
  mvBoundary_rankThreeFacet_or_codimensionTwo D.exponent_boundary

end HC4.Newton
