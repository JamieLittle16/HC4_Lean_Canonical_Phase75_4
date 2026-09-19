import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitSecondSourceLayer
import Mathlib.Tactic

/-!
# Full source reflection at the first-deficit second interaction

The second-interaction theorem already proves reflection in the two deficit
coordinates.  The source-honest finite staircase supplies two additional
affine equations on every carrier exponent.  Therefore the same reflection
propagates to the longitudinal and final transverse coordinates.

Thus the three forced source monomials are an honest arithmetic progression
in the full four-dimensional exponent lattice.  No subpolynomial is declared
singular and no new Rees clock is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- **The first three forced deficit layers are a full source arithmetic
progression.** -/
theorem firstDeficit_fullSourceReflection
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ first opposite second : Fin 4 →₀ ℕ,
      first ∈ P.carrier.support ∧
      opposite ∈ P.carrier.support ∧
      second ∈ P.carrier.support ∧
      first ≠ opposite ∧
      opposite ≠ second ∧
      ∀ i : Fin 4, first i + second i = 2 * opposite i := by
  rcases firstDeficit_reflectedSecondLayerGeometry_export
      G hthree houtThree with H
  cases H with
  | left first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop2 hqj
      hsecond hsecondOrder hsecond2 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have h1 : first 1 + second 1 = 2 * opposite 1 := by
        rw [hfirst1]
        exact hreflect
      have h2 : first 2 + second 2 = 2 * opposite 2 := by
        omega
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hsChord := F.support_deficit_chord hthree houtThree hsecond
      have hcoef :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        have hell : (0 : ℤ) < (F.locked.ell : ℤ) := by
          exact_mod_cast F.locked.ell_pos
        have hn : (1 : ℤ) < (F.highest.n : ℤ) := by
          exact_mod_cast (show 1 < F.highest.n by omega)
        omega
      have h1Z :
          (first 1 : ℤ) + (second 1 : ℤ) =
            2 * (opposite 1 : ℤ) := by
        exact_mod_cast h1
      have h2Z :
          (first 2 : ℤ) + (second 2 : ℤ) =
            2 * (opposite 2 : ℤ) := by
        exact_mod_cast h2
      have h0Z :
          (first 0 : ℤ) + (second 0 : ℤ) =
            2 * (opposite 0 : ℤ) := by
        nlinarith [hfChord, hoChord, hsChord]
      have h0 : first 0 + second 0 = 2 * opposite 0 := by
        exact_mod_cast h0Z

      have hfCurve := (F.support_staircase_equations
        hthree houtThree hfirstP).2
      have hoCurve := (F.support_staircase_equations
        hthree houtThree hop).2
      have hsCurve := (F.support_staircase_equations
        hthree houtThree hsecond).2
      simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
        HC4.Polynomial.rankThreeQuotientCoordinate_pair,
        HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
        one_mul] at hfCurve hoCurve hsCurve
      push_cast at hfCurve hoCurve hsCurve
      have h3Z :
          (first 3 : ℤ) + (second 3 : ℤ) =
            2 * (opposite 3 : ℤ) := by
        nlinarith [hfCurve, hoCurve, hsCurve, h0Z, h1Z, h2Z]
      have h3 : first 3 + second 3 = 2 * opposite 3 := by
        exact_mod_cast h3Z

      refine ⟨first, opposite, second, hfirstP, hop, hsecond, ?_, ?_, ?_⟩
      · intro heq
        have hcoord := congrArg (fun e : Fin 4 →₀ ℕ => e 2) heq
        rw [hfirst2, hop2] at hcoord
        omega
      · intro heq
        have hcoord := congrArg (fun e : Fin 4 →₀ ℕ => e 2) heq
        rw [hop2, hsecond2] at hcoord
        omega
      · intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3

  | right first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop1 hqj
      hsecond hsecondOrder hsecond1 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have h1 : first 1 + second 1 = 2 * opposite 1 := by
        omega
      have h2 : first 2 + second 2 = 2 * opposite 2 := by
        rw [hfirst2]
        exact hreflect
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hsChord := F.support_deficit_chord hthree houtThree hsecond
      have hcoef :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        have hell : (0 : ℤ) < (F.locked.ell : ℤ) := by
          exact_mod_cast F.locked.ell_pos
        have hn : (1 : ℤ) < (F.highest.n : ℤ) := by
          exact_mod_cast (show 1 < F.highest.n by omega)
        omega
      have h1Z :
          (first 1 : ℤ) + (second 1 : ℤ) =
            2 * (opposite 1 : ℤ) := by
        exact_mod_cast h1
      have h2Z :
          (first 2 : ℤ) + (second 2 : ℤ) =
            2 * (opposite 2 : ℤ) := by
        exact_mod_cast h2
      have h0Z :
          (first 0 : ℤ) + (second 0 : ℤ) =
            2 * (opposite 0 : ℤ) := by
        nlinarith [hfChord, hoChord, hsChord]
      have h0 : first 0 + second 0 = 2 * opposite 0 := by
        exact_mod_cast h0Z

      have hfCurve := (F.support_staircase_equations
        hthree houtThree hfirstP).2
      have hoCurve := (F.support_staircase_equations
        hthree houtThree hop).2
      have hsCurve := (F.support_staircase_equations
        hthree houtThree hsecond).2
      simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
        HC4.Polynomial.rankThreeQuotientCoordinate_pair,
        HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
        one_mul] at hfCurve hoCurve hsCurve
      push_cast at hfCurve hoCurve hsCurve
      have h3Z :
          (first 3 : ℤ) + (second 3 : ℤ) =
            2 * (opposite 3 : ℤ) := by
        nlinarith [hfCurve, hoCurve, hsCurve, h0Z, h1Z, h2Z]
      have h3 : first 3 + second 3 = 2 * opposite 3 := by
        exact_mod_cast h3Z

      refine ⟨first, opposite, second, hfirstP, hop, hsecond, ?_, ?_, ?_⟩
      · intro heq
        have hcoord := congrArg (fun e : Fin 4 →₀ ℕ => e 1) heq
        rw [hfirst1, hop1] at hcoord
        omega
      · intro heq
        have hcoord := congrArg (fun e : Fin 4 →₀ ℕ => e 1) heq
        rw [hop1, hsecond1] at hcoord
        omega
      · intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
