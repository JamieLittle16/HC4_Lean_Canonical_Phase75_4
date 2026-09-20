import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitFullReflection
import Mathlib.Tactic

/-!
# Longitudinal descent of the first reflected source progression

The repaired second-interaction chain produces three actual source monomials
first, opposite, second in exact arithmetic progression. The missing deficit
coordinate rises by one from first to opposite, while the other deficit
coordinate does not decrease. On the finite-staircase source chord this forces
the longitudinal coordinate e0 to decrease strictly.

Together with full source reflection the same strict decrease occurs from
opposite to second. This is the well-founded arithmetic input for the finite
reflected-source closure; no repair clock or auxiliary valuation is used.
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

/-- The two affine staircase equations propagate arithmetic reflection
from coordinates 0,1,2 to the final source coordinate.  Keeping this as a
small declaration avoids exposing the full descent context to `nlinarith`. -/
private theorem sourceReflection_three
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite second : Fin 4 →₀ ℕ}
    (hfirst : first ∈ P.carrier.support)
    (hop : opposite ∈ P.carrier.support)
    (hsecond : second ∈ P.carrier.support)
    (h0Z :
      (first 0 : ℤ) + (second 0 : ℤ) = 2 * (opposite 0 : ℤ))
    (h1Z :
      (first 1 : ℤ) + (second 1 : ℤ) = 2 * (opposite 1 : ℤ))
    (h2Z :
      (first 2 : ℤ) + (second 2 : ℤ) = 2 * (opposite 2 : ℤ)) :
    first 3 + second 3 = 2 * opposite 3 := by
  have hfCurve := (F.support_staircase_equations hthree houtThree hfirst).2
  have hoCurve := (F.support_staircase_equations hthree houtThree hop).2
  have hsCurve := (F.support_staircase_equations hthree houtThree hsecond).2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at hfCurve hoCurve hsCurve
  push_cast at hfCurve hoCurve hsCurve
  have h3Z :
      (first 3 : ℤ) + (second 3 : ℤ) =
        2 * (opposite 3 : ℤ) := by
    nlinarith only [hfCurve, hoCurve, hsCurve, h0Z, h1Z, h2Z]
  exact_mod_cast h3Z

/-- **Central deficit-chord difference.**

Relative to the retained central monomial, every actual carrier exponent has
longitudinal drop exactly equal to its weighted transverse deficit.  This is
the integral lattice equation underlying the reflected-source endgame. -/
theorem central_deficit_chord_difference
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) :
    ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
        ((G.central 0 : ℤ) - (e 0 : ℤ)) =
      (F.locked.ell : ℤ) * (e 1 : ℤ) +
        ((F.highest.n : ℤ) - 1) * (e 2 : ℤ) := by
  have hc := F.support_deficit_chord hthree houtThree G.central_mem
  have hec := F.support_deficit_chord hthree houtThree he
  rw [G.central_one_zero, G.central_two_zero] at hc
  norm_num at hc
  nlinarith only [hc, hec]

/-- The first reflected source progression descends strictly in the
longitudinal coordinate. -/
theorem firstDeficit_fullSourceReflection_longitudinalDescent
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ first opposite second : Fin 4 →₀ ℕ,
      first ∈ P.carrier.support ∧
      opposite ∈ P.carrier.support ∧
      second ∈ P.carrier.support ∧
      first ≠ opposite ∧
      opposite ≠ second ∧
      (∀ i : Fin 4, first i + second i = 2 * opposite i) ∧
      second 0 < opposite 0 ∧
      opposite 0 < first 0 := by
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
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hcoef :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      have hop1ge : q ≤ opposite 1 := by
        rw [hj] at hqj
        rw [hop2] at hqj
        omega
      have h1stepZ :
          (0 : ℤ) ≤ (opposite 1 : ℤ) - (first 1 : ℤ) := by
        rw [hfirst1]
        have hop1geZ : (q : ℤ) ≤ (opposite 1 : ℤ) := by
          exact_mod_cast hop1ge
        exact sub_nonneg.mpr hop1geZ
      have h2stepZ :
          (0 : ℤ) < (opposite 2 : ℤ) - (first 2 : ℤ) := by
        rw [hop2, hfirst2]
        norm_num
      have hfirst0opp0Z :
          (opposite 0 : ℤ) < (first 0 : ℤ) := by
        nlinarith only [hfChord, hoChord, h1stepZ, h2stepZ,
          hellZ, hnZ, hcoef]
      have hfirst0opp0 : opposite 0 < first 0 := by
        exact_mod_cast hfirst0opp0Z
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
      have hsecond0opp0 : second 0 < opposite 0 := by
        omega

      have h3 : first 3 + second 3 = 2 * opposite 3 :=
        sourceReflection_three F hthree houtThree
          hfirstP hop hsecond h0Z h1Z h2Z
      have hneFO : first ≠ opposite := by
        intro heq
        have hc : first 2 = opposite 2 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 2) heq
        rw [hfirst2, hop2] at hc
        omega
      have hneOS : opposite ≠ second := by
        intro heq
        have hc : opposite 2 = second 2 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 2) heq
        rw [hop2, hsecond2] at hc
        omega
      refine ⟨first, opposite, second, hfirstP, hop, hsecond,
        hneFO, hneOS, ?_, hsecond0opp0, hfirst0opp0⟩
      intro i
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
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hcoef :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      have hop2ge : q ≤ opposite 2 := by
        rw [hj] at hqj
        rw [hop1] at hqj
        omega
      have h1stepZ :
          (0 : ℤ) < (opposite 1 : ℤ) - (first 1 : ℤ) := by
        rw [hop1, hfirst1]
        norm_num
      have h2stepZ :
          (0 : ℤ) ≤ (opposite 2 : ℤ) - (first 2 : ℤ) := by
        rw [hfirst2]
        have hop2geZ : (q : ℤ) ≤ (opposite 2 : ℤ) := by
          exact_mod_cast hop2ge
        exact sub_nonneg.mpr hop2geZ
      have hfirst0opp0Z :
          (opposite 0 : ℤ) < (first 0 : ℤ) := by
        nlinarith only [hfChord, hoChord, h1stepZ, h2stepZ,
          hellZ, hnZ, hcoef]
      have hfirst0opp0 : opposite 0 < first 0 := by
        exact_mod_cast hfirst0opp0Z
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
      have hsecond0opp0 : second 0 < opposite 0 := by
        omega

      have h3 : first 3 + second 3 = 2 * opposite 3 :=
        sourceReflection_three F hthree houtThree
          hfirstP hop hsecond h0Z h1Z h2Z
      have hneFO : first ≠ opposite := by
        intro heq
        have hc : first 1 = opposite 1 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 1) heq
        rw [hfirst1, hop1] at hc
        omega
      have hneOS : opposite ≠ second := by
        intro heq
        have hc : opposite 1 = second 1 := by
          simpa using congrArg (fun e : Fin 4 →₀ ℕ => e 1) heq
        rw [hop1, hsecond1] at hc
        omega
      refine ⟨first, opposite, second, hfirstP, hop, hsecond,
        hneFO, hneOS, ?_, hsecond0opp0, hfirst0opp0⟩
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3


/-- **The first opposite opening is separated by at least two deficit orders.**

The first reflected layer is pure on one deficit axis, while the first later
opening of the opposite axis has exponent exactly one in that missing
coordinate.  A hypothetical order gap one would make the other deficit
coordinate unchanged.  Subtracting the exact source staircase chords would
then force a positive multiple of `ell+n-1` to equal one of its proper
positive summands, which is impossible.

This is entirely source arithmetic; no further determinant coefficient or
auxiliary clock is used. -/
theorem firstDeficit_oppositeOrder_gap_two_le
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ opposite : Fin 4 →₀ ℕ,
      opposite ∈ P.carrier.support ∧
      G.firstDeficitOrder + 2 ≤ opposite 1 + opposite 2 ∧
      (opposite 2 = 1 ∨ opposite 1 = 1) := by
  rcases firstDeficit_reflectedSecondLayerGeometry_export
      G hthree houtThree with H
  cases H with
  | left first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop2 hqj
      hsecond hsecondOrder hsecond2 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hcoefPos :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      have hgap : q + 2 ≤ j := by
        by_contra hnot
        have hjEq : j = q + 1 := by omega
        have hop1 : opposite 1 = q := by
          rw [hj, hop2] at hjEq
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have hdiffEq :
            ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              (F.highest.n : ℤ) - 1 := by
          nlinarith only [hfChord, hoChord]
        have hdiffPos :
            (0 : ℤ) < (first 0 : ℤ) - (opposite 0 : ℤ) := by
          nlinarith only [hdiffEq, hnZ, hcoefPos]
        have hdiffOne :
            (1 : ℤ) ≤ (first 0 : ℤ) - (opposite 0 : ℤ) := by
          omega
        have hcoefGt :
            (F.highest.n : ℤ) - 1 <
              (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
          linarith
        nlinarith only [hdiffEq, hdiffOne, hcoefGt, hcoefPos]
      refine ⟨opposite, hop, ?_, Or.inl hop2⟩
      rw [← hq, ← hj]
      exact hgap

  | right first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop1 hqj
      hsecond hsecondOrder hsecond1 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hcoefPos :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      have hgap : q + 2 ≤ j := by
        by_contra hnot
        have hjEq : j = q + 1 := by omega
        have hop2 : opposite 2 = q := by
          rw [hj, hop1] at hjEq
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have hdiffEq :
            ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              (F.locked.ell : ℤ) := by
          nlinarith only [hfChord, hoChord]
        have hdiffPos :
            (0 : ℤ) < (first 0 : ℤ) - (opposite 0 : ℤ) := by
          nlinarith only [hdiffEq, hellZ, hcoefPos]
        have hdiffOne :
            (1 : ℤ) ≤ (first 0 : ℤ) - (opposite 0 : ℤ) := by
          omega
        have hcoefGt :
            (F.locked.ell : ℤ) <
              (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
          omega
        nlinarith only [hdiffEq, hdiffOne, hcoefGt, hcoefPos]
      refine ⟨opposite, hop, ?_, Or.inr hop1⟩
      rw [← hq, ← hj]
      exact hgap


/-- **The primitive opposite opening lies in a finite endpoint window.**

In the left orientation the least source point opening deficit coordinate
`2` occurs no later than the literal locked outside endpoint, whose total
deficit is `ell`.  In the right orientation the symmetric minimum occurs no
later than the literal primitive-highest `e1` endpoint, whose total deficit
is `n-1`.

Together with the two-order separation above this traps the first reflected
opening in a finite source interval. -/
theorem firstDeficit_primitiveOppositeOpening_interval
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ opposite : Fin 4 →₀ ℕ,
        opposite ∈ P.carrier.support ∧
        opposite 2 = 1 ∧
        G.firstDeficitOrder + 2 ≤ opposite 1 + opposite 2 ∧
        opposite 1 + opposite 2 ≤ F.locked.ell) ∨
      (∃ opposite : Fin 4 →₀ ℕ,
        opposite ∈ P.carrier.support ∧
        opposite 1 = 1 ∧
        G.firstDeficitOrder + 2 ≤ opposite 1 + opposite 2 ∧
        opposite 1 + opposite 2 ≤ F.highest.n - 1) := by
  rcases G.firstDeficit_primitiveOppositeOpening hthree houtThree with ⟨O⟩
  cases O with
  | left first opposite hfirst hfirst1 hfirst2 huniq
      hop hop2 hstrict hminimal =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hcoefPos :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      let j := opposite 1 + opposite 2
      have hgap : G.firstDeficitOrder + 2 ≤ j := by
        by_contra hnot
        have hjEq : j = G.firstDeficitOrder + 1 := by
          dsimp [j] at *
          omega
        have hop1 : opposite 1 = G.firstDeficitOrder := by
          dsimp [j] at hjEq
          rw [hop2] at hjEq
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have hdiffEq :
            ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              (F.highest.n : ℤ) - 1 := by
          nlinarith only [hfChord, hoChord]
        have hdiffPos :
            (0 : ℤ) < (first 0 : ℤ) - (opposite 0 : ℤ) := by
          nlinarith only [hdiffEq, hnZ, hcoefPos]
        have hdiffOne :
            (1 : ℤ) ≤ (first 0 : ℤ) - (opposite 0 : ℤ) := by
          omega
        have hcoefGt :
            (F.highest.n : ℤ) - 1 <
              (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
          linarith
        nlinarith only [hdiffEq, hdiffOne, hcoefGt, hcoefPos]
      have houtMem :
          C.ray.outsideExponent ∈ P.carrier.support :=
        F.locked.outside_provenance.carrier_mem
      have hout2 : 0 < C.ray.outsideExponent 2 := by
        rw [F.locked.outside_two]
        exact F.locked.ell_pos
      have hupper := hminimal C.ray.outsideExponent houtMem hout2
      rw [F.locked.outside_one, F.locked.outside_two] at hupper
      norm_num at hupper
      exact Or.inl ⟨opposite, hop, hop2, by simpa [j] using hgap, hupper⟩

  | right first opposite hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hcoefPos :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      let j := opposite 1 + opposite 2
      have hgap : G.firstDeficitOrder + 2 ≤ j := by
        by_contra hnot
        have hjEq : j = G.firstDeficitOrder + 1 := by
          dsimp [j] at *
          omega
        have hop2 : opposite 2 = G.firstDeficitOrder := by
          dsimp [j] at hjEq
          rw [hop1] at hjEq
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have hdiffEq :
            ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              (F.locked.ell : ℤ) := by
          nlinarith only [hfChord, hoChord]
        have hdiffPos :
            (0 : ℤ) < (first 0 : ℤ) - (opposite 0 : ℤ) := by
          nlinarith only [hdiffEq, hellZ, hcoefPos]
        have hdiffOne :
            (1 : ℤ) ≤ (first 0 : ℤ) - (opposite 0 : ℤ) := by
          omega
        have hcoefGt :
            (F.locked.ell : ℤ) <
              (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
          omega
        nlinarith only [hdiffEq, hdiffOne, hcoefGt, hcoefPos]
      have hhighMem : F.highest.e1 ∈ P.carrier.support :=
        F.highest.e1_provenance.carrier_mem
      have hhigh1 : 0 < F.highest.e1 1 := by
        rw [F.highest.e1_one]
        have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
        omega
      have hupper := hminimal F.highest.e1 hhighMem hhigh1
      rw [F.highest.e1_one, F.highest.e1_two] at hupper
      norm_num at hupper
      exact Or.inr ⟨opposite, hop, hop1, by simpa [j] using hgap, hupper⟩


/-- **There are no reflected opening gaps three or four.**

The source lattice equation rules out the two orders immediately after the
unit locked-line step.  Thus the first primitive opposite opening either has
the exact unit-line gap `2`, or it lies at least five total-deficit orders
after the first layer. -/
theorem firstDeficit_oppositeOrder_eq_add_two_or_add_five_le
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ opposite : Fin 4 →₀ ℕ,
        opposite ∈ P.carrier.support ∧
        opposite 1 + opposite 2 = G.firstDeficitOrder + 2 ∧
        (opposite 2 = 1 ∨ opposite 1 = 1)) ∨
      (∃ opposite : Fin 4 →₀ ℕ,
        opposite ∈ P.carrier.support ∧
        G.firstDeficitOrder + 5 ≤ opposite 1 + opposite 2 ∧
        (opposite 2 = 1 ∨ opposite 1 = 1)) := by
  rcases firstDeficit_reflectedSecondLayerGeometry_export
      G hthree houtThree with H
  cases H with
  | left first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop2 hqj
      hsecond hsecondOrder hsecond2 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hnell : F.highest.n ≤ F.locked.ell := by
        have hsep := F.highest_n_lt_locked_height hthree houtThree
        omega
      have hMpos :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      have hstep :
          ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
              (((first 0 : ℤ) - (opposite 0 : ℤ)) - 1) =
            (F.locked.ell : ℤ) *
              (((j : ℤ) - (q : ℤ)) - 2) := by
        rw [hfirst1, hfirst2] at hfChord
        have hop1 : opposite 1 = j - 1 := by
          rw [hj, hop2]
          omega
        rw [hop1, hop2] at hoChord
        push_cast at hfChord hoChord
        norm_num at hfChord hoChord
        nlinarith only [hfChord, hoChord]
      by_cases hunit : j = q + 2
      · exact Or.inl ⟨opposite, hop, by
          rw [← hq, ← hj]
          exact hunit, Or.inl hop2⟩
      · have hfive : q + 5 ≤ j := by
          by_contra hnot
          have hcases : j = q + 3 ∨ j = q + 4 := by omega
          rcases hcases with hthreeGap | hfourGap
          · have hEq :
                ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                    (((first 0 : ℤ) - (opposite 0 : ℤ)) - 1) =
                  (F.locked.ell : ℤ) := by
              rw [hthreeGap] at hstep
              norm_num at hstep
              exact hstep
            have hDpos :
                (0 : ℤ) <
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              nlinarith only [hEq, hellZ, hMpos]
            have hDone :
                (1 : ℤ) ≤
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              omega
            nlinarith only [hEq, hDone, hMpos, hnZ]
          · have hEq :
                ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                    (((first 0 : ℤ) - (opposite 0 : ℤ)) - 1) =
                  2 * (F.locked.ell : ℤ) := by
              rw [hfourGap] at hstep
              norm_num at hstep
              nlinarith only [hstep]
            have hDpos :
                (0 : ℤ) <
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              nlinarith only [hEq, hellZ, hMpos]
            have hDone :
                (1 : ℤ) ≤
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              omega
            have hDltTwo :
                ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 < 2 := by
              by_contra hnotlt
              have hDtwo :
                  (2 : ℤ) ≤
                    ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
                exact le_of_not_gt hnotlt
              nlinarith only [hEq, hDtwo, hnZ, hellZ, hMpos]
            have hDoneEq :
                ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 = 1 := by
              omega
            rw [hDoneEq, mul_one] at hEq
            have hnEq :
                (F.highest.n : ℤ) - 1 = (F.locked.ell : ℤ) := by
              nlinarith only [hEq]
            have hnEqNat : F.highest.n - 1 = F.locked.ell := by
              exact_mod_cast hnEq
            omega
      exact Or.inr ⟨opposite, hop, by
        rw [← hq, ← hj]
        exact hfive, Or.inl hop2⟩

  | right first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop1 hqj
      hsecond hsecondOrder hsecond1 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        exact_mod_cast (show 1 < F.highest.n by omega)
      have hnell : F.highest.n ≤ F.locked.ell := by
        have hsep := F.highest_n_lt_locked_height hthree houtThree
        omega
      have hMpos :
          (0 : ℤ) <
            (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
        omega
      have hstep :
          ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
              (((first 0 : ℤ) - (opposite 0 : ℤ)) - 1) =
            ((F.highest.n : ℤ) - 1) *
              (((j : ℤ) - (q : ℤ)) - 2) := by
        rw [hfirst1, hfirst2] at hfChord
        have hop2 : opposite 2 = j - 1 := by
          rw [hj, hop1]
          omega
        rw [hop1, hop2] at hoChord
        push_cast at hfChord hoChord
        norm_num at hfChord hoChord
        nlinarith only [hfChord, hoChord]
      by_cases hunit : j = q + 2
      · exact Or.inl ⟨opposite, hop, by
          rw [← hq, ← hj]
          exact hunit, Or.inr hop1⟩
      · have hfive : q + 5 ≤ j := by
          by_contra hnot
          have hcases : j = q + 3 ∨ j = q + 4 := by omega
          rcases hcases with hthreeGap | hfourGap
          · have hEq :
                ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                    (((first 0 : ℤ) - (opposite 0 : ℤ)) - 1) =
                  (F.highest.n : ℤ) - 1 := by
              rw [hthreeGap] at hstep
              norm_num at hstep
              exact hstep
            have hDpos :
                (0 : ℤ) <
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              nlinarith only [hEq, hnZ, hMpos]
            have hDone :
                (1 : ℤ) ≤
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              omega
            nlinarith only [hEq, hDone, hMpos, hellZ]
          · have hEq :
                ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
                    (((first 0 : ℤ) - (opposite 0 : ℤ)) - 1) =
                  2 * ((F.highest.n : ℤ) - 1) := by
              rw [hfourGap] at hstep
              norm_num at hstep
              nlinarith only [hstep]
            have hDpos :
                (0 : ℤ) <
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              nlinarith only [hEq, hnZ, hMpos]
            have hDone :
                (1 : ℤ) ≤
                  ((first 0 : ℤ) - (opposite 0 : ℤ)) - 1 := by
              omega
            have hMgt :
                2 * ((F.highest.n : ℤ) - 1) <
                  (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
              have hnellZ : (F.highest.n : ℤ) ≤ (F.locked.ell : ℤ) := by
                exact_mod_cast hnell
              nlinarith
            nlinarith only [hEq, hDone, hMgt, hMpos]
      exact Or.inr ⟨opposite, hop, by
        rw [← hq, ← hj]
        exact hfive, Or.inr hop1⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
