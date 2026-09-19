import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitSecondSourceLayer
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneNoInteriorSupport
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

/-- The central survivor cannot lie in the endpoint-only four-term
staircase.  Its honest source monomial has both deficit coordinates zero,
whereas every endpoint retained by `NoStrictInteriorSupport` has at least one
of those coordinates positive. -/
theorem central_not_noStrictInterior
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    ¬ F.NoStrictInteriorSupport := by
  intro hno
  have hsupp := F.support_eq_locked_highest_of_noStrictInterior hno
  have hmem : G.central ∈
      ({C.ray.facetExponent, C.ray.outsideExponent,
        F.highest.e0, F.highest.e1} : Finset (Fin 4 →₀ ℕ)) := by
    rw [← hsupp]
    exact G.central_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hfacet | hout | hhigh0 | hhigh1
  · have h1 := congrArg (fun e : Fin 4 →₀ ℕ => e (1 : Fin 4)) hfacet
    rw [G.central_one_zero, F.locked.facet_one] at h1
    omega
  · have h2 := congrArg (fun e : Fin 4 →₀ ℕ => e (2 : Fin 4)) hout
    rw [G.central_two_zero, F.locked.outside_two] at h2
    exact (Nat.ne_of_gt F.locked.ell_pos) h2.symm
  · have h1 := congrArg (fun e : Fin 4 →₀ ℕ => e (1 : Fin 4)) hhigh0
    rw [G.central_one_zero, F.highest.e0_one] at h1
    have hn : 0 < F.highest.n := lt_of_lt_of_le (by decide : 0 < 2)
      F.highest.n_two_le
    exact (Nat.ne_of_gt hn) h1.symm
  · have h1 := congrArg (fun e : Fin 4 →₀ ℕ => e (1 : Fin 4)) hhigh1
    rw [G.central_one_zero, F.highest.e1_one] at h1
    have hn : 0 < F.highest.n - 1 := by omega
    exact (Nat.ne_of_gt hn) h1.symm

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
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
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
        nlinarith only [hfChord, hoChord, hsChord, h1Z, h2Z, hcoef]
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
        nlinarith only [hfCurve, hoCurve, hsCurve, h0Z, h1Z, h2Z]
      have h3 : first 3 + second 3 = 2 * opposite 3 := by
        exact_mod_cast h3Z

      refine ⟨first, opposite, second, hfirstP, hop, hsecond, ?_, ?_, ?_⟩
      · intro heq
        have hcoord : first 2 = opposite 2 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 2) heq
        rw [hfirst2, hop2] at hcoord
        omega
      · intro heq
        have hcoord : opposite 2 = second 2 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 2) heq
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
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
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
        nlinarith only [hfChord, hoChord, hsChord, h1Z, h2Z, hcoef]
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
        nlinarith only [hfCurve, hoCurve, hsCurve, h0Z, h1Z, h2Z]
      have h3 : first 3 + second 3 = 2 * opposite 3 := by
        exact_mod_cast h3Z

      refine ⟨first, opposite, second, hfirstP, hop, hsecond, ?_, ?_, ?_⟩
      · intro heq
        have hcoord : first 1 = opposite 1 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 1) heq
        rw [hfirst1, hop1] at hcoord
        omega
      · intro heq
        have hcoord : opposite 1 = second 1 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 1) heq
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
