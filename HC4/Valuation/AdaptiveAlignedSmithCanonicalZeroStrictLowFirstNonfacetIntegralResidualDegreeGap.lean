import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralLockedFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetResidualDegreeGap
import Mathlib.Tactic

/-!
# A19.99: integral contact sharpens the strict-low residual degree gap

A19.87 retains an actual nonlinear codimension-two monomial of the represented
strict-low source whose omitted `.qs` coordinate has multiplicity at least two.
A19.98 supplies, on the same represented source, an integral first-contact
weight

    ordinaryDegree4 d + r * d[0] <= topDegree

with `r >= 2` in the surviving different-facet branch.  Evaluating that source
inequality on the retained codimension-two monomial therefore contributes at
least `2 * 2 = 4` units in the omitted direction.

This sharpens A19.89's previously available `+3` ordinary-degree gap to `+4`.
The statement remains entirely source-native: no new progress measure, balance
hypothesis, carrier transport, or planar/JC2 reduction is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **A19.99 integral strict-low residual gap.**  In the genuine lower `.qs`
other-facet branch, one retained codimension-two source monomial lies at least
four ordinary degrees below the original maximal top face.  The witnessing
integral contact slope is retained as well. -/
theorem qs_ray_otherFacet_integral_strictLow_source_degree_add_four_le_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    ∃ r : ℕ, ∃ d : Fin 4 →₀ ℕ,
      2 ≤ r ∧
      d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support ∧
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d ∧
      HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) ≤
        T.topFace.degree ∧
      HC4.Polynomial.ordinaryDegree4 d + 4 ≤ T.topFace.degree := by
  rcases C.qs_ray_otherFacet_integral_locked_source_contact
      hthree hne houtThree with
    ⟨r, hr, _hbump, hsource, _hray, _hlock⟩
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨d, hd, hdeg, hd0, hcodim⟩
  have hcontact := hsource hd
  have hfour : 4 ≤ r * d (0 : Fin 4) := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ r * d (0 : Fin 4) := Nat.mul_le_mul hr hd0
  have hgap :
      HC4.Polynomial.ordinaryDegree4 d + 4 ≤ T.topFace.degree := by
    omega
  exact ⟨r, d, hr, hd, hdeg, hd0, hcodim, hcontact, hgap⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
