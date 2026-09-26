import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitReflectionDescent
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseInterface
import Mathlib.Tactic

/-!
# Finite-staircase closure of the reflected central deficit packet

The source-honest central-deficit chain produces a canonical three-layer
reflection.  This file begins the final finite closure by converting that
packet into the actual quotient-staircase alternatives.

The first transition is deliberately source-only:

* a minimal two-order opening gives three distinct source monomials in one
  normalized `(1,V)` quotient fibre;
* every other opening is separated by at least five total-deficit orders.

No auxiliary clock or repair state is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem no_integer_multiple_between_zero_one
    (D c t : ℤ)
    (hD : 0 < D) (hc : 0 < c) (hcD : c < D)
    (h : D * t = c) : False := by
  have ht0 : 0 < t := by
    nlinarith
  have ht1 : t < 1 := by
    nlinarith
  omega

private theorem no_integer_multiple_between_one_two
    (D c t : ℤ)
    (hD : 0 < D) (hc : 0 < c) (hcD : c < D)
    (h : D * t = D + c) : False := by
  have ht1 : 1 < t := by
    nlinarith
  have ht2 : t < 2 := by
    nlinarith
  omega

private theorem no_integer_multiple_between_two_three
    (D c t : ℤ)
    (hD : 0 < D) (hDc : D < c) (hc2D : c < 2 * D)
    (h : D * t = D + c) : False := by
  have ht2 : 2 < t := by
    nlinarith
  have ht3 : t < 3 := by
    nlinarith
  omega

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

/-- Three distinct actual source monomials lying in one normalized
`(1,V)` quotient fibre. -/
structure FirstDeficitGapTwoFiberData where
  first : Fin 4 →₀ ℕ
  opposite : Fin 4 →₀ ℕ
  second : Fin 4 →₀ ℕ
  first_mem : first ∈ P.carrier.support
  opposite_mem : opposite ∈ P.carrier.support
  second_mem : second ∈ P.carrier.support
  first_ne_opposite : first ≠ opposite
  opposite_ne_second : opposite ≠ second
  first_quotient_eq_opposite :
    HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V first =
      HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite
  opposite_quotient_eq_second :
    HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite =
      HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V second

/-- Three actual reflected source points which move strictly through the
finite-staircase pair coordinate. -/
structure FirstDeficitSeparatedPairData where
  first : Fin 4 →₀ ℕ
  opposite : Fin 4 →₀ ℕ
  second : Fin 4 →₀ ℕ
  first_mem : first ∈ P.carrier.support
  opposite_mem : opposite ∈ P.carrier.support
  second_mem : second ∈ P.carrier.support
  gap_five :
    G.firstDeficitOrder + 5 ≤ opposite 1 + opposite 2
  pair_order :
    ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V first).pair <
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair ∧
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair <
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V second).pair) ∨
    ((HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V second).pair <
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair ∧
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair <
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V first).pair)

/-- **First finite-staircase transition.**

For the canonical reflected second layer, either the opening gap is exactly
two and the three reflected source monomials are three distinct points of one
normalized quotient fibre, or the first opposite opening is separated from
the first deficit order by at least five.

The exclusion of gaps one, three, and four is integral source arithmetic on
the exact staircase chord. -/
theorem firstDeficit_gapTwoFiber_or_fiveGap
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (FirstDeficitGapTwoFiberData (P := P) (F := F)) ∨
      Nonempty (FirstDeficitSeparatedPairData (P := P) (F := F) G) := by
  rcases G.firstDeficit_reflectedSecondLayerGeometry_export
      hthree houtThree with H
  cases H with
  | left first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop2 hqj
      hsecond hsecondOrder hsecond2 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hsChord := F.support_deficit_chord hthree houtThree hsecond
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hn2 : 2 ≤ F.highest.n := F.highest.n_two_le
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        exact_mod_cast hn2
      have hsep := F.highest_n_lt_locked_height hthree houtThree
      have hnle : F.highest.n ≤ F.locked.ell := by omega
      have hnleZ : (F.highest.n : ℤ) ≤ (F.locked.ell : ℤ) := by
        exact_mod_cast hnle
      let D : ℤ :=
        (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1
      have hD : 0 < D := by
        dsimp [D]
        omega

      have hgap1 : j ≠ q + 1 := by
        intro hgap
        have hop1 : opposite 1 = q := by
          rw [hj, hop2] at hgap
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have heq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              (F.highest.n : ℤ) - 1 := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hc : (0 : ℤ) < (F.highest.n : ℤ) - 1 := by omega
        have hcD :
            (F.highest.n : ℤ) - 1 < D := by
          dsimp [D]
          omega
        exact no_integer_multiple_between_zero_one
          D ((F.highest.n : ℤ) - 1)
          ((first 0 : ℤ) - (opposite 0 : ℤ))
          hD hc hcD heq

      have hgap3 : j ≠ q + 3 := by
        intro hgap
        have hop1 : opposite 1 = q + 2 := by
          rw [hj, hop2] at hgap
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have heq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              D + (F.locked.ell : ℤ) := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hcD : (F.locked.ell : ℤ) < D := by
          dsimp [D]
          omega
        exact no_integer_multiple_between_one_two
          D (F.locked.ell : ℤ)
          ((first 0 : ℤ) - (opposite 0 : ℤ))
          hD hellZ hcD heq

      have hgap4 : j ≠ q + 4 := by
        intro hgap
        have hop1 : opposite 1 = q + 3 := by
          rw [hj, hop2] at hgap
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have heq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              D + 2 * (F.locked.ell : ℤ) := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hDc : D < 2 * (F.locked.ell : ℤ) := by
          dsimp [D]
          omega
        have hc2D : 2 * (F.locked.ell : ℤ) < 2 * D := by
          dsimp [D]
          omega
        exact no_integer_multiple_between_two_three
          D (2 * (F.locked.ell : ℤ))
          ((first 0 : ℤ) - (opposite 0 : ℤ))
          hD hDc hc2D heq

      by_cases hgap2 : j = q + 2
      · left
        have hop1 : opposite 1 = q + 1 := by
          rw [hj, hop2] at hgap2
          omega
        have hsecond1 : second 1 = q + 2 := by
          rw [hop1] at hreflect
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        rw [hsecond1, hsecond2] at hsChord
        norm_num at hfChord hoChord hsChord
        have hfoEq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) = D := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hosEq :
            D * ((opposite 0 : ℤ) - (second 0 : ℤ)) = D := by
          dsimp [D]
          linear_combination hoChord - hsChord
        have hfoDiff :
            (first 0 : ℤ) - (opposite 0 : ℤ) = 1 := by
          apply mul_left_cancel₀ (ne_of_gt hD)
          simpa using hfoEq
        have hosDiff :
            (opposite 0 : ℤ) - (second 0 : ℤ) = 1 := by
          apply mul_left_cancel₀ (ne_of_gt hD)
          simpa using hosEq
        have hfoZ :
            (first 0 : ℤ) = (opposite 0 : ℤ) + 1 := by
          omega
        have hosZ :
            (opposite 0 : ℤ) = (second 0 : ℤ) + 1 := by
          omega
        have hfo : first 0 = opposite 0 + 1 := by
          exact_mod_cast hfoZ
        have hos : opposite 0 = second 0 + 1 := by
          exact_mod_cast hosZ
        have hpairFO :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V first).pair =
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          omega
        have hpairOS :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair =
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V second).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          omega
        have hqFO :=
          F.support_quotient_eq_of_pair_eq hfirstP hop hpairFO
        have hqOS :=
          F.support_quotient_eq_of_pair_eq hop hsecond hpairOS
        refine ⟨{
          first := first
          opposite := opposite
          second := second
          first_mem := hfirstP
          opposite_mem := hop
          second_mem := hsecond
          first_ne_opposite := ?_
          opposite_ne_second := ?_
          first_quotient_eq_opposite := hqFO
          opposite_quotient_eq_second := hqOS
        }⟩
        · intro heq
          have hc : first (2 : Fin 4) = opposite (2 : Fin 4) :=
            congrArg (fun e : Fin 4 →₀ ℕ => e (2 : Fin 4)) heq
          omega
        · intro heq
          have hc : opposite (2 : Fin 4) = second (2 : Fin 4) :=
            congrArg (fun e : Fin 4 →₀ ℕ => e (2 : Fin 4)) heq
          omega
      · right
        have hfar : q + 5 ≤ j := by
          by_contra hnot
          have hle : j ≤ q + 4 := by omega
          have hcases :
              j = q + 1 ∨ j = q + 2 ∨ j = q + 3 ∨ j = q + 4 := by
            omega
          rcases hcases with h1 | h2 | h3 | h4
          · exact hgap1 h1
          · exact hgap2 h2
          · exact hgap3 h3
          · exact hgap4 h4
        have hgapFive :
            G.firstDeficitOrder + 5 ≤ opposite 1 + opposite 2 := by
          rw [← hq, ← hj]
          exact hfar
        have hop1Lower : q + 4 ≤ opposite 1 := by
          rw [hj, hop2] at hfar
          omega
        have hdeltaZ :
            (0 : ℤ) <
              (opposite 1 : ℤ) - (q : ℤ) - 1 := by
          omega
        have hrhsPos :
            (0 : ℤ) <
              ((F.highest.n : ℤ) - 1) *
                ((opposite 1 : ℤ) - (q : ℤ) - 1) := by
          exact mul_pos (by omega) hdeltaZ
        have hreflectZ :
            (q : ℤ) + (second 1 : ℤ) =
              2 * (opposite 1 : ℤ) := by
          exact_mod_cast hreflect
        have hf := hfChord
        have ho := hoChord
        have hs := hsChord
        rw [hfirst1, hfirst2] at hf
        rw [hop2] at ho
        rw [hsecond2] at hs
        norm_num at hf ho hs
        have hscaleFO :
            D * (((opposite 0 : ℤ) + (opposite 1 : ℤ)) -
              ((first 0 : ℤ) + (q : ℤ))) =
              ((F.highest.n : ℤ) - 1) *
                ((opposite 1 : ℤ) - (q : ℤ) - 1) := by
          dsimp [D]
          linear_combination ho - hf
        have hscaleOS :
            D * (((second 0 : ℤ) + (second 1 : ℤ)) -
              ((opposite 0 : ℤ) + (opposite 1 : ℤ))) =
              ((F.highest.n : ℤ) - 1) *
                ((opposite 1 : ℤ) - (q : ℤ) - 1) := by
          dsimp [D]
          linear_combination hs - ho +
            ((F.highest.n : ℤ) - 1) * hreflectZ
        have hdeltaFO :
            (0 : ℤ) <
              ((opposite 0 : ℤ) + (opposite 1 : ℤ)) -
                ((first 0 : ℤ) + (q : ℤ)) := by
          have hprod :
              (0 : ℤ) <
                D * (((opposite 0 : ℤ) + (opposite 1 : ℤ)) -
                  ((first 0 : ℤ) + (q : ℤ))) := by
            rw [hscaleFO]
            exact hrhsPos
          rcases (mul_pos_iff.mp hprod) with hpos | hneg
          · exact hpos.2
          · omega
        have hdeltaOS :
            (0 : ℤ) <
              ((second 0 : ℤ) + (second 1 : ℤ)) -
                ((opposite 0 : ℤ) + (opposite 1 : ℤ)) := by
          have hprod :
              (0 : ℤ) <
                D * (((second 0 : ℤ) + (second 1 : ℤ)) -
                  ((opposite 0 : ℤ) + (opposite 1 : ℤ))) := by
            rw [hscaleOS]
            exact hrhsPos
          rcases (mul_pos_iff.mp hprod) with hpos | hneg
          · exact hpos.2
          · omega
        have hpairFOZ :
            (first 0 : ℤ) + (q : ℤ) <
              (opposite 0 : ℤ) + (opposite 1 : ℤ) := by
          omega
        have hpairOSZ :
            (opposite 0 : ℤ) + (opposite 1 : ℤ) <
              (second 0 : ℤ) + (second 1 : ℤ) := by
          omega
        have hpairFO :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V first).pair <
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          rw [hfirst1]
          omega
        have hpairOS :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair <
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V second).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          omega
        exact ⟨{
          first := first
          opposite := opposite
          second := second
          first_mem := hfirstP
          opposite_mem := hop
          second_mem := hsecond
          gap_five := hgapFive
          pair_order := Or.inl ⟨hpairFO, hpairOS⟩
        }⟩

  | right first opposite second q j k hq hj hk
      hfirst hfirst1 hfirst2 hop hop1 hqj
      hsecond hsecondOrder hsecond1 hreflect =>
      have hfirstP : first ∈ P.carrier.support :=
        (G.firstDeficitLayer_support hfirst).1
      have hfChord := F.support_deficit_chord hthree houtThree hfirstP
      have hoChord := F.support_deficit_chord hthree houtThree hop
      have hsChord := F.support_deficit_chord hthree houtThree hsecond
      have hellZ : (0 : ℤ) < (F.locked.ell : ℤ) := by
        exact_mod_cast F.locked.ell_pos
      have hn2 : 2 ≤ F.highest.n := F.highest.n_two_le
      have hnZ : (1 : ℤ) < (F.highest.n : ℤ) := by
        exact_mod_cast hn2
      have hsep := F.highest_n_lt_locked_height hthree houtThree
      have hnle : F.highest.n ≤ F.locked.ell := by omega
      let D : ℤ :=
        (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1
      have hD : 0 < D := by
        dsimp [D]
        omega
      have hn1Z : (0 : ℤ) < (F.highest.n : ℤ) - 1 := by omega

      have hgap1 : j ≠ q + 1 := by
        intro hgap
        have hop2 : opposite 2 = q := by
          rw [hj, hop1] at hgap
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have heq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              (F.locked.ell : ℤ) := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hcD : (F.locked.ell : ℤ) < D := by
          dsimp [D]
          omega
        exact no_integer_multiple_between_zero_one
          D (F.locked.ell : ℤ)
          ((first 0 : ℤ) - (opposite 0 : ℤ))
          hD hellZ hcD heq

      have hgap3 : j ≠ q + 3 := by
        intro hgap
        have hop2 : opposite 2 = q + 2 := by
          rw [hj, hop1] at hgap
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have heq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              D + ((F.highest.n : ℤ) - 1) := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hcD : (F.highest.n : ℤ) - 1 < D := by
          dsimp [D]
          omega
        exact no_integer_multiple_between_one_two
          D ((F.highest.n : ℤ) - 1)
          ((first 0 : ℤ) - (opposite 0 : ℤ))
          hD hn1Z hcD heq

      have hgap4 : j ≠ q + 4 := by
        intro hgap
        have hop2 : opposite 2 = q + 3 := by
          rw [hj, hop1] at hgap
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        norm_num at hfChord hoChord
        have heq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) =
              D + 2 * ((F.highest.n : ℤ) - 1) := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hc : (0 : ℤ) < 2 * ((F.highest.n : ℤ) - 1) := by
          omega
        have hcD :
            2 * ((F.highest.n : ℤ) - 1) < D := by
          dsimp [D]
          omega
        exact no_integer_multiple_between_one_two
          D (2 * ((F.highest.n : ℤ) - 1))
          ((first 0 : ℤ) - (opposite 0 : ℤ))
          hD hc hcD heq

      by_cases hgap2 : j = q + 2
      · left
        have hop2 : opposite 2 = q + 1 := by
          rw [hj, hop1] at hgap2
          omega
        have hsecond2 : second 2 = q + 2 := by
          rw [hop2] at hreflect
          omega
        rw [hfirst1, hfirst2] at hfChord
        rw [hop1, hop2] at hoChord
        rw [hsecond1, hsecond2] at hsChord
        norm_num at hfChord hoChord hsChord
        have hfoEq :
            D * ((first 0 : ℤ) - (opposite 0 : ℤ)) = D := by
          dsimp [D]
          linear_combination hfChord - hoChord
        have hosEq :
            D * ((opposite 0 : ℤ) - (second 0 : ℤ)) = D := by
          dsimp [D]
          linear_combination hoChord - hsChord
        have hfoDiff :
            (first 0 : ℤ) - (opposite 0 : ℤ) = 1 := by
          apply mul_left_cancel₀ (ne_of_gt hD)
          simpa using hfoEq
        have hosDiff :
            (opposite 0 : ℤ) - (second 0 : ℤ) = 1 := by
          apply mul_left_cancel₀ (ne_of_gt hD)
          simpa using hosEq
        have hfoZ :
            (first 0 : ℤ) = (opposite 0 : ℤ) + 1 := by
          omega
        have hosZ :
            (opposite 0 : ℤ) = (second 0 : ℤ) + 1 := by
          omega
        have hfo : first 0 = opposite 0 + 1 := by
          exact_mod_cast hfoZ
        have hos : opposite 0 = second 0 + 1 := by
          exact_mod_cast hosZ
        have hpairFO :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V first).pair =
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          omega
        have hpairOS :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair =
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V second).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          omega
        have hqFO :=
          F.support_quotient_eq_of_pair_eq hfirstP hop hpairFO
        have hqOS :=
          F.support_quotient_eq_of_pair_eq hop hsecond hpairOS
        refine ⟨{
          first := first
          opposite := opposite
          second := second
          first_mem := hfirstP
          opposite_mem := hop
          second_mem := hsecond
          first_ne_opposite := ?_
          opposite_ne_second := ?_
          first_quotient_eq_opposite := hqFO
          opposite_quotient_eq_second := hqOS
        }⟩
        · intro heq
          have hc : first (1 : Fin 4) = opposite (1 : Fin 4) :=
            congrArg (fun e : Fin 4 →₀ ℕ => e (1 : Fin 4)) heq
          omega
        · intro heq
          have hc : opposite (1 : Fin 4) = second (1 : Fin 4) :=
            congrArg (fun e : Fin 4 →₀ ℕ => e (1 : Fin 4)) heq
          omega
      · right
        have hfar : q + 5 ≤ j := by
          by_contra hnot
          have hle : j ≤ q + 4 := by omega
          have hcases :
              j = q + 1 ∨ j = q + 2 ∨ j = q + 3 ∨ j = q + 4 := by
            omega
          rcases hcases with h1 | h2 | h3 | h4
          · exact hgap1 h1
          · exact hgap2 h2
          · exact hgap3 h3
          · exact hgap4 h4
        have hgapFive :
            G.firstDeficitOrder + 5 ≤ opposite 1 + opposite 2 := by
          rw [← hq, ← hj]
          exact hfar
        have hop2Lower : q + 4 ≤ opposite 2 := by
          rw [hj, hop1] at hfar
          omega
        have hdeltaZ :
            (0 : ℤ) <
              (opposite 2 : ℤ) - (q : ℤ) - 1 := by
          omega
        have hrhsPos :
            (0 : ℤ) <
              ((F.highest.n : ℤ) - 1) *
                ((opposite 2 : ℤ) - (q : ℤ) - 1) := by
          exact mul_pos (by omega) hdeltaZ
        have hreflectZ :
            (q : ℤ) + (second 2 : ℤ) =
              2 * (opposite 2 : ℤ) := by
          exact_mod_cast hreflect
        have hf := hfChord
        have ho := hoChord
        have hs := hsChord
        rw [hfirst1, hfirst2] at hf
        rw [hop1] at ho
        rw [hsecond1] at hs
        norm_num at hf ho hs
        have hscaleFO :
            D * ((first 0 : ℤ) -
              ((opposite 0 : ℤ) + 1)) =
              ((F.highest.n : ℤ) - 1) *
                ((opposite 2 : ℤ) - (q : ℤ) - 1) := by
          dsimp [D]
          linear_combination hf - ho
        have hscaleOS :
            D * (((opposite 0 : ℤ) + 1) -
              ((second 0 : ℤ) + 2)) =
              ((F.highest.n : ℤ) - 1) *
                ((opposite 2 : ℤ) - (q : ℤ) - 1) := by
          dsimp [D]
          linear_combination ho - hs +
            ((F.highest.n : ℤ) - 1) * hreflectZ
        have hdeltaOF :
            (0 : ℤ) <
              (first 0 : ℤ) - ((opposite 0 : ℤ) + 1) := by
          have hprod :
              (0 : ℤ) <
                D * ((first 0 : ℤ) - ((opposite 0 : ℤ) + 1)) := by
            rw [hscaleFO]
            exact hrhsPos
          rcases (mul_pos_iff.mp hprod) with hpos | hneg
          · exact hpos.2
          · omega
        have hdeltaSO :
            (0 : ℤ) <
              ((opposite 0 : ℤ) + 1) - ((second 0 : ℤ) + 2) := by
          have hprod :
              (0 : ℤ) <
                D * (((opposite 0 : ℤ) + 1) -
                  ((second 0 : ℤ) + 2)) := by
            rw [hscaleOS]
            exact hrhsPos
          rcases (mul_pos_iff.mp hprod) with hpos | hneg
          · exact hpos.2
          · omega
        have hpairOFZ :
            (opposite 0 : ℤ) + 1 < (first 0 : ℤ) := by
          omega
        have hpairSOZ :
            (second 0 : ℤ) + 2 <
              (opposite 0 : ℤ) + 1 := by
          omega
        have hpairOF :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair <
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V first).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          rw [hop1, hfirst1]
          omega
        have hpairSO :
            (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V second).pair <
              (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V opposite).pair := by
          simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair]
          rw [hsecond1, hop1]
          omega
        exact ⟨{
          first := first
          opposite := opposite
          second := second
          first_mem := hfirstP
          opposite_mem := hop
          second_mem := hsecond
          gap_five := hgapFive
          pair_order := Or.inr ⟨hpairSO, hpairOF⟩
        }⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
