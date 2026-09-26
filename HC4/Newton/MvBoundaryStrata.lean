import HC4.Newton.BoundaryStrata
import HC4.Polynomial.FourExponent
import Mathlib.Tactic

/-!
# A18.5.19: multivariate boundary exponents enter the toric stratum split

The Newton/valuation side of the HC4 proof works with genuine
`MvPolynomial (Fin 4)` exponents, while the verified toric boundary
classification is stated for `HC4.Toric.Exponent`.

`HC4.Polynomial.toToricExponent` is already the exact coordinatewise bridge.
This file packages the composition needed by the terminal edge argument:
an actual balanced multivariate exponent which omits a coordinate is either
rank three in the relative interior of one toric facet, or lies on one of the
four extreme transition rays.

No convex-geometric hypothesis is added here.  The boundary premise is the
literal `MvExponentOnBoundary` conclusion produced by `InteriorVertex`.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric

/-- A genuine multivariate monomial is rank three on a facet when its toric
four-tuple lies in the relative interior of that facet. -/
def MvRankThreeOnFacet
    (F : ToricFacet) (d : Fin 4 →₀ ℕ) : Prop :=
  RankThreeOnFacet F (toToricExponent d)

/-- The exact coordinate content of a multivariate rank-three facet point. -/
theorem mvRankThreeOnFacet_iff
    (F : ToricFacet) (d : Fin 4 →₀ ℕ) :
    MvRankThreeOnFacet F d ↔
      match F with
      | .pr => d 1 = 0 ∧ 0 < d 0 ∧ 0 < d 2 ∧ 0 < d 3
      | .rq => d 3 = 0 ∧ 0 < d 0 ∧ 0 < d 1 ∧ 0 < d 2
      | .qs => d 0 = 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3
      | .sp => d 2 = 0 ∧ 0 < d 0 ∧ 0 < d 1 ∧ 0 < d 3 := by
  cases F <;> rfl

/-- **Balanced multivariate boundary stratum split.**

This is `boundary_rankThree_or_extremeRay` with no loss of provenance from the
actual `MvPolynomial` exponent. -/
theorem mvBoundary_rankThree_or_extremeRay
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {d : Fin 4 →₀ ℕ}
    (hBal : IsBalancedExponent a b d)
    (hbdry : MvExponentOnBoundary d) :
    (∃ F : ToricFacet, MvRankThreeOnFacet F d) ∨
      (∃ F G : ToricFacet,
        AdjacentFacets F G ∧ OnRay a b F G (toToricExponent d)) := by
  have hBal' : Balanced a b (toToricExponent d) :=
    (isBalancedExponent_iff_balanced a b d).1 hBal
  rcases boundary_rankThree_or_extremeRay ha hb hcop hBal' hbdry with
    hthree | hray
  · rcases hthree with ⟨F, hF⟩
    exact Or.inl ⟨F, hF⟩
  · exact Or.inr hray

/-- In the `qs` chart (the chart omitting coordinate `0`) the abstract
rank-three alternative is exactly positivity of the three Smith-transverse
coordinates. -/
theorem mvRankThreeOnFacet_qs
    {d : Fin 4 →₀ ℕ}
    (h : MvRankThreeOnFacet .qs d) :
    d 0 = 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3 := by
  exact h

end HC4.Newton
