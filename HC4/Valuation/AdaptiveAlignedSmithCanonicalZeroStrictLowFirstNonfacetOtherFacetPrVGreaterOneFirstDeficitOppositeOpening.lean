import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitRankThreeRoof
import Mathlib.Tactic

/-!
# First honest opening of the opposite central-deficit coordinate

After binary Hesse rigidity, the least positive total-deficit layer is one
source monomial on a single deficit axis. The opposite axis must nevertheless
appear later because the original source-honest carrier still contains both
locked roof endpoints.

This file selects, directly from the finite carrier support, the least
total-deficit source monomial which opens the missing coordinate and proves
that its order is strictly larger than the first deficit order.

No determinant argument is used here. This is only the finite-support
selector required by the subsequent rank-three first-break calculation.
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

/-- Any positive total-deficit carrier monomial occurs no earlier than the
canonical first positive deficit layer. -/
theorem firstDeficitOrder_le_total_of_carrier_mem
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hpos : 0 < e 1 + e 2) :
    G.firstDeficitOrder ≤ e 1 + e 2 := by
  let k := e 1 + e 2
  have heLayer :
      e ∈ (familyParameterLayer P.centralDeficitFamily k).support := by
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨he, rfl⟩
  have hcoeff :
      (MvPolynomial.coeff e P.centralDeficitFamily).coeff k ≠ 0 := by
    rw [← familyParameterLayer_coeff]
    exact MvPolynomial.mem_support_iff.mp heLayer
  have heFamily : e ∈ P.centralDeficitFamily.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  have hk :
      k ∈ familyParameterLayerOrders P.centralDeficitFamily := by
    exact (mem_familyParameterLayerOrders_iff
      P.centralDeficitFamily k).2 ⟨e, heFamily, hcoeff⟩
  simpa [firstDeficitOrder, k] using
    firstPositiveActualParameterOrder_le
      P.centralDeficitFamily
      (centralDeficitFamily_hasPositiveActualLayer G)
      hk hpos

/-- If the first layer lies on the second-coordinate-zero axis, there is a
least later carrier point with positive second deficit. -/
theorem exists_first_twoOpening_of_first_oneAxis
    {first : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first) :
    ∃ e : Fin 4 →₀ ℕ,
      e ∈ P.carrier.support ∧
      0 < e 2 ∧
      G.firstDeficitOrder < e 1 + e 2 ∧
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        e 1 + e 2 ≤ f 1 + f 2 := by
  let U : Finset (Fin 4 →₀ ℕ) :=
    P.carrier.support.filter (fun e => 0 < e 2)
  have hU : U.Nonempty := by
    rcases F.locked_yRoof_mem with ⟨he, _h0, _h1, h2, _h3⟩
    refine ⟨C.ray.outsideExponent, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    rw [h2]
    exact F.locked.ell_pos
  rcases Finset.exists_min_image U (fun e => e 1 + e 2) hU with
    ⟨e, heU, hmin⟩
  have heCarrier : e ∈ P.carrier.support :=
    (Finset.mem_filter.mp heU).1
  have he2 : 0 < e 2 := (Finset.mem_filter.mp heU).2
  have htotalPos : 0 < e 1 + e 2 := by omega
  have hqle : G.firstDeficitOrder ≤ e 1 + e 2 :=
    G.firstDeficitOrder_le_total_of_carrier_mem heCarrier htotalPos
  have hstrict : G.firstDeficitOrder < e 1 + e 2 := by
    rcases lt_or_eq_of_le hqle with hlt | heq
    · exact hlt
    · have heLayer :
          e ∈ G.firstDeficitLayer.support := by
        rw [firstDeficitLayer]
        rw [P.centralDeficitFamily_layer_mem_iff]
        exact ⟨heCarrier, heq.symm⟩
      have heFirst : e = first := huniq e heLayer
      have hz : e 2 = 0 := by simpa [heFirst] using hfirst2
      omega
  refine ⟨e, heCarrier, he2, hstrict, ?_⟩
  intro f hf hf2
  exact hmin f (Finset.mem_filter.mpr ⟨hf, hf2⟩)

/-- Symmetrically, if the first layer lies on the first-coordinate-zero axis,
there is a least later carrier point with positive first deficit. -/
theorem exists_first_oneOpening_of_first_twoAxis
    {first : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first) :
    ∃ e : Fin 4 →₀ ℕ,
      e ∈ P.carrier.support ∧
      0 < e 1 ∧
      G.firstDeficitOrder < e 1 + e 2 ∧
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        e 1 + e 2 ≤ f 1 + f 2 := by
  let U : Finset (Fin 4 →₀ ℕ) :=
    P.carrier.support.filter (fun e => 0 < e 1)
  have hU : U.Nonempty := by
    rcases F.highest_zRoof_mem with ⟨he, _h0, h1, _h2, _h3⟩
    refine ⟨F.highest.e1, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    rw [h1]
    have hnTwo : 2 ≤ F.highest.n := F.highest.n_two_le
    omega
  rcases Finset.exists_min_image U (fun e => e 1 + e 2) hU with
    ⟨e, heU, hmin⟩
  have heCarrier : e ∈ P.carrier.support :=
    (Finset.mem_filter.mp heU).1
  have he1 : 0 < e 1 := (Finset.mem_filter.mp heU).2
  have htotalPos : 0 < e 1 + e 2 := by omega
  have hqle : G.firstDeficitOrder ≤ e 1 + e 2 :=
    G.firstDeficitOrder_le_total_of_carrier_mem heCarrier htotalPos
  have hstrict : G.firstDeficitOrder < e 1 + e 2 := by
    rcases lt_or_eq_of_le hqle with hlt | heq
    · exact hlt
    · have heLayer :
          e ∈ G.firstDeficitLayer.support := by
        rw [firstDeficitLayer]
        rw [P.centralDeficitFamily_layer_mem_iff]
        exact ⟨heCarrier, heq.symm⟩
      have heFirst : e = first := huniq e heLayer
      have hz : e 1 = 0 := by simpa [heFirst] using hfirst1
      omega
  refine ⟨e, heCarrier, he1, hstrict, ?_⟩
  intro f hf hf1
  exact hmin f (Finset.mem_filter.mpr ⟨hf, hf1⟩)

/-- Source-honest first opposite-opening package. -/
inductive FirstDeficitOppositeOpening : Type u
  | left
      (first opposite : Fin 4 →₀ ℕ)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = G.firstDeficitOrder)
      (first_two : first 2 = 0)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two_pos : 0 < opposite 2)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 2 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)
  | right
      (first opposite : Fin 4 →₀ ℕ)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = G.firstDeficitOrder)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one_pos : 0 < opposite 1)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 1 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)

/-- The axis singleton and the two retained source endpoints canonically
produce the first later opening of the missing deficit coordinate. -/
theorem firstDeficit_oppositeOpening
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty G.FirstDeficitOppositeOpening := by
  rcases G.firstDeficitLayer_singleton_axis hthree houtThree with
    hleft | hright
  · rcases hleft with ⟨first, hmem, h1, h2, huniq⟩
    rcases G.exists_first_twoOpening_of_first_oneAxis
      hmem h1 h2 huniq with
      ⟨opposite, hopMem, hop2, hstrict, hmin⟩
    exact ⟨.left first opposite hmem h1 h2 huniq
      hopMem hop2 hstrict hmin⟩
  · rcases hright with ⟨first, hmem, h1, h2, huniq⟩
    rcases G.exists_first_oneOpening_of_first_twoAxis
      hmem h1 h2 huniq with
      ⟨opposite, hopMem, hop1, hstrict, hmin⟩
    exact ⟨.right first opposite hmem h1 h2 huniq
      hopMem hop1 hstrict hmin⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
