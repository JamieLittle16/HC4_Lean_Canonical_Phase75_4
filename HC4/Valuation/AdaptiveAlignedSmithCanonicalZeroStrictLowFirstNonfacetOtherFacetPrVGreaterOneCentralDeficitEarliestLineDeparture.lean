import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitReflectedLineDeparture
import Mathlib.Tactic

/-!
# Earliest reflected-line departure in total-deficit order

The previous module selects the first missing-coordinate stratum which falls
below the reflected line.  For the determinant coefficient argument the more
useful selector is the dual one: choose the least *total-deficit parameter
order* containing any such bad source point, then within that exact layer
choose one with maximal missing-coordinate exponent.

This has two consequences used downstream:

* every positive parameter layer strictly before the selected order obeys the
  reflected affine support bound;
* at the selected order, the chosen source monomial is a top-weight term for
  the reflected tilt.

No new clock is introduced: the selected order is literally `e₁+e₂` in the
honest central-deficit Rees family.
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

/-- Canonical earliest bad total-deficit layer, with a maximal missing
exponent chosen inside that layer. -/
inductive FirstDeficitEarliestReflectedLineDepartureData : Prop
  | left
      (q J s m : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (q_lt_J : q < J)
      (depart : Fin 4 →₀ ℕ)
      (depart_mem : depart ∈ P.carrier.support)
      (depart_order : depart 1 + depart 2 = s)
      (depart_missing : depart 2 = m)
      (m_three_le : 3 ≤ m)
      (depart_below :
        s < q + m * (J - q))
      (first_missing_minimal :
        ∀ f ∈ P.carrier.support, 0 < f 2 → J ≤ f 1 + f 2)
      (second_missing_minimal :
        ∀ f ∈ P.carrier.support,
          2 ≤ f 2 → q + 2 * (J - q) ≤ f 1 + f 2)
      (earliest :
        ∀ f ∈ P.carrier.support,
          3 ≤ f 2 →
          f 1 + f 2 < q + f 2 * (J - q) →
          s ≤ f 1 + f 2)
      (maximal_missing :
        ∀ f ∈ P.carrier.support,
          f 1 + f 2 = s →
          3 ≤ f 2 →
          f 1 + f 2 < q + f 2 * (J - q) →
          f 2 ≤ m)
  | right
      (q J s m : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (q_lt_J : q < J)
      (depart : Fin 4 →₀ ℕ)
      (depart_mem : depart ∈ P.carrier.support)
      (depart_order : depart 1 + depart 2 = s)
      (depart_missing : depart 1 = m)
      (m_three_le : 3 ≤ m)
      (depart_below :
        s < q + m * (J - q))
      (first_missing_minimal :
        ∀ f ∈ P.carrier.support, 0 < f 1 → J ≤ f 1 + f 2)
      (second_missing_minimal :
        ∀ f ∈ P.carrier.support,
          2 ≤ f 1 → q + 2 * (J - q) ≤ f 1 + f 2)
      (earliest :
        ∀ f ∈ P.carrier.support,
          3 ≤ f 1 →
          f 1 + f 2 < q + f 1 * (J - q) →
          s ≤ f 1 + f 2)
      (maximal_missing :
        ∀ f ∈ P.carrier.support,
          f 1 + f 2 = s →
          3 ≤ f 1 →
          f 1 + f 2 < q + f 1 * (J - q) →
          f 1 ≤ m)

/-- Select the least bad total-deficit order and then the largest missing
exponent among the bad monomials at that exact order.  The same packet retains
the first- and second-missing lower bounds proved by the staggered determinant
calculation. -/
theorem firstDeficit_earliestReflectedLineDeparture
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitEarliestReflectedLineDepartureData := by
  have hqTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  cases G.firstDeficit_secondMissingOpening hthree houtThree with
  | left first opposite q J Kord hq hJ hK
      hfirst hfirst1 hfirst2 hop hop2 hqJ hmin1 hmin2
      second hsecond hsecondOrder hsecond2 hsecondUnique hKle =>
      rcases F.locked_yRoof_mem with
        ⟨hlocked, _hlocked0, hlocked1, hlocked2, _hlocked3⟩
      have hqTwo' : 2 ≤ q := by
        rw [hq]
        exact hqTwo
      have hKFour : 4 ≤ Kord := by
        rw [hK]
        omega
      have hellFour : 4 ≤ F.locked.ell :=
        le_trans hKFour hKle
      have hdPos : 0 < J - q := Nat.sub_pos_of_lt hqJ
      have hbelow :
          C.ray.outsideExponent 1 + C.ray.outsideExponent 2 <
            q + C.ray.outsideExponent 2 * (J - q) := by
        rw [hlocked1, hlocked2]
        have hdOne : 1 ≤ J - q := by omega
        have hmul :
            F.locked.ell ≤ F.locked.ell * (J - q) := by
          simpa using Nat.mul_le_mul_left F.locked.ell hdOne
        omega
      let pred : ℕ → Prop := fun s =>
        ∃ f : Fin 4 →₀ ℕ,
          f ∈ P.carrier.support ∧
          3 ≤ f 2 ∧
          f 1 + f 2 = s ∧
          f 1 + f 2 < q + f 2 * (J - q)
      have hex : ∃ s, pred s := by
        refine ⟨C.ray.outsideExponent 1 + C.ray.outsideExponent 2,
          C.ray.outsideExponent, hlocked, ?_, rfl, hbelow⟩
        rw [hlocked2]
        omega
      let s := Nat.find hex
      have hsSpec : pred s := Nat.find_spec hex
      rcases hsSpec with ⟨f0, hf0, hf03, hf0s, hf0bad⟩
      let B : Finset (Fin 4 →₀ ℕ) :=
        P.carrier.support.filter fun f =>
          3 ≤ f 2 ∧
          f 1 + f 2 = s ∧
          f 1 + f 2 < q + f 2 * (J - q)
      have hB : B.Nonempty := by
        exact ⟨f0, Finset.mem_filter.mpr
          ⟨hf0, hf03, hf0s, hf0bad⟩⟩
      rcases Finset.exists_max_image B (fun f => f 2) hB with
        ⟨depart, hdepartB, hmax⟩
      rcases Finset.mem_filter.mp hdepartB with
        ⟨hdepart, hm3', horder, hbad⟩
      let m := depart 2
      have hmin2' :
          ∀ f ∈ P.carrier.support,
            2 ≤ f 2 → q + 2 * (J - q) ≤ f 1 + f 2 := by
        intro f hf hf2
        have h := hmin2 f hf hf2
        rw [hK] at h
        omega
      refine .left q J s m hq hqJ depart hdepart horder rfl hm3'
        (by simpa [m, horder] using hbad) hmin1 hmin2' ?_ ?_
      · intro g hg hg3 hgbad
        apply Nat.find_min' hex
        exact ⟨g, hg, hg3, rfl, hgbad⟩
      · intro g hg hgs hg3 hgbad
        have hgB : g ∈ B :=
          Finset.mem_filter.mpr ⟨hg, hg3, hgs, hgbad⟩
        simpa [m] using hmax g hgB

  | right first opposite q J Kord hq hJ hK
      hfirst hfirst1 hfirst2 hop hop1 hqJ hmin1 hmin2
      second hsecond hsecondOrder hsecond1 hsecondUnique hKle =>
      rcases F.highest_zRoof_mem with
        ⟨hhigh, _hhigh0, hhigh1, hhigh2, _hhigh3⟩
      have hqTwo' : 2 ≤ q := by
        rw [hq]
        exact hqTwo
      have hKFour : 4 ≤ Kord := by
        rw [hK]
        omega
      have hnFour : 4 ≤ F.highest.n - 1 :=
        le_trans hKFour hKle
      have hdPos : 0 < J - q := Nat.sub_pos_of_lt hqJ
      have hbelow :
          F.highest.e1 1 + F.highest.e1 2 <
            q + F.highest.e1 1 * (J - q) := by
        rw [hhigh1, hhigh2]
        have hdOne : 1 ≤ J - q := by omega
        have hmul :
            F.highest.n - 1 ≤
              (F.highest.n - 1) * (J - q) := by
          simpa using Nat.mul_le_mul_left (F.highest.n - 1) hdOne
        omega
      let pred : ℕ → Prop := fun s =>
        ∃ f : Fin 4 →₀ ℕ,
          f ∈ P.carrier.support ∧
          3 ≤ f 1 ∧
          f 1 + f 2 = s ∧
          f 1 + f 2 < q + f 1 * (J - q)
      have hex : ∃ s, pred s := by
        refine ⟨F.highest.e1 1 + F.highest.e1 2,
          F.highest.e1, hhigh, ?_, rfl, hbelow⟩
        rw [hhigh1]
        omega
      let s := Nat.find hex
      have hsSpec : pred s := Nat.find_spec hex
      rcases hsSpec with ⟨f0, hf0, hf03, hf0s, hf0bad⟩
      let B : Finset (Fin 4 →₀ ℕ) :=
        P.carrier.support.filter fun f =>
          3 ≤ f 1 ∧
          f 1 + f 2 = s ∧
          f 1 + f 2 < q + f 1 * (J - q)
      have hB : B.Nonempty := by
        exact ⟨f0, Finset.mem_filter.mpr
          ⟨hf0, hf03, hf0s, hf0bad⟩⟩
      rcases Finset.exists_max_image B (fun f => f 1) hB with
        ⟨depart, hdepartB, hmax⟩
      rcases Finset.mem_filter.mp hdepartB with
        ⟨hdepart, hm3', horder, hbad⟩
      let m := depart 1
      have hmin2' :
          ∀ f ∈ P.carrier.support,
            2 ≤ f 1 → q + 2 * (J - q) ≤ f 1 + f 2 := by
        intro f hf hf1
        have h := hmin2 f hf hf1
        rw [hK] at h
        omega
      refine .right q J s m hq hqJ depart hdepart horder rfl hm3'
        (by simpa [m, horder] using hbad) hmin1 hmin2' ?_ ?_
      · intro g hg hg3 hgbad
        apply Nat.find_min' hex
        exact ⟨g, hg, hg3, rfl, hgbad⟩
      · intro g hg hgs hg3 hgbad
        have hgB : g ∈ B :=
          Finset.mem_filter.mpr ⟨hg, hg3, hgs, hgbad⟩
        simpa [m] using hmax g hgB

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
