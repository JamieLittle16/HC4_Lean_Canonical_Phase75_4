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
exponent among the bad monomials at that exact order. -/
theorem firstDeficit_earliestReflectedLineDeparture
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitEarliestReflectedLineDepartureData := by
  cases G.firstDeficit_reflectedLineDeparture hthree houtThree with
  | left q J hq hqJ witness hwitness hm3 hbelow =>
      let pred : ℕ → Prop := fun s =>
        ∃ f : Fin 4 →₀ ℕ,
          f ∈ P.carrier.support ∧
          3 ≤ f 2 ∧
          f 1 + f 2 = s ∧
          f 1 + f 2 < q + f 2 * (J - q)
      have hex : ∃ s, pred s := by
        refine ⟨witness 1 + witness 2, witness, hwitness, hm3, rfl, hbelow⟩
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
      have hdata := Finset.mem_filter.mp hdepartB
      rcases hdata with ⟨hdepart, hm3', horder, hbad⟩
      let m := depart 2
      refine .left q J s m hq hqJ depart hdepart horder rfl hm3'
        (by simpa [m] using hbad) ?_ ?_
      · intro g hg hg3 hgbad
        apply Nat.find_min' hex
        exact ⟨g, hg, hg3, rfl, hgbad⟩
      · intro g hg hgs hg3 hgbad
        have hgB : g ∈ B := by
          exact Finset.mem_filter.mpr ⟨hg, hg3, hgs, hgbad⟩
        simpa [m] using hmax g hgB

  | right q J hq hqJ witness hwitness hm3 hbelow =>
      let pred : ℕ → Prop := fun s =>
        ∃ f : Fin 4 →₀ ℕ,
          f ∈ P.carrier.support ∧
          3 ≤ f 1 ∧
          f 1 + f 2 = s ∧
          f 1 + f 2 < q + f 1 * (J - q)
      have hex : ∃ s, pred s := by
        refine ⟨witness 1 + witness 2, witness, hwitness, hm3, rfl, hbelow⟩
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
      have hdata := Finset.mem_filter.mp hdepartB
      rcases hdata with ⟨hdepart, hm3', horder, hbad⟩
      let m := depart 1
      refine .right q J s m hq hqJ depart hdepart horder rfl hm3'
        (by simpa [m] using hbad) ?_ ?_
      · intro g hg hg3 hgbad
        apply Nat.find_min' hex
        exact ⟨g, hg, hg3, rfl, hgbad⟩
      · intro g hg hgs hg3 hgbad
        have hgB : g ∈ B := by
          exact Finset.mem_filter.mpr ⟨hg, hg3, hgs, hgbad⟩
        simpa [m] using hmax g hgB

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
