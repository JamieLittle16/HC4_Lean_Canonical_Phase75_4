import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightSourceDeficits
import Mathlib.Tactic

/-!
# Source-honest lower hull of the mirrored finite staircase

For the right `(V,1)` branch we project the actual carrier to source deficits
`(e₁,e₃)`.  The locked outside endpoint lies on `e₁=0`, while the primitive
highest endpoint lies on `e₃=0`.  The finite maximal-slope selector therefore
gives the exact mirror of the left lower-hull alternative.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

structure QsOtherFacetPrRightVLowerHullData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) where
  lo : Fin 4 →₀ ℕ
  edge : Fin 4 →₀ ℕ
  lo_mem : lo ∈ P.carrier.support
  edge_mem : edge ∈ P.carrier.support
  lo_one_zero : lo 1 = 0
  lo_three_pos : 0 < lo 3
  edge_one_pos : 0 < edge 1
  edge_three_lt : edge 3 < lo 3
  lower_bound :
    ∀ e ∈ P.carrier.support,
      (edge 1 : ℤ) * (lo 3 : ℤ) ≤
        ((lo 3 : ℤ) - (edge 3 : ℤ)) * (e 1 : ℤ) +
          (edge 1 : ℤ) * (e 3 : ℤ)

/-- Either the right source carrier already contains a central `e₁=e₃=0`
point, or it has an honest positive lower-hull wall leaving the `e₁=0` roof. -/
theorem QsOtherFacetPrRightVContactFrontierData.central_or_lowerHull
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ e ∈ P.carrier.support, e 1 = 0 ∧ e 3 = 0) ∨
      Nonempty (QsOtherFacetPrRightVLowerHullData F) := by
  classical
  by_cases hcentral : ∃ e ∈ P.carrier.support, e 1 = 0 ∧ e 3 = 0
  · exact Or.inl hcentral
  · right

    let p : (Fin 4 →₀ ℕ) → ℤ := fun e => (e 1 : ℤ)
    let s : (Fin 4 →₀ ℕ) → ℤ := fun e => -(e 3 : ℤ)

    rcases F.locked_yRoof_mem with
      ⟨hLmem, _hL0, hL1, _hL2, _hL3⟩
    rcases F.highest_wRoof_mem with
      ⟨hHmem, _hH0, hH1, _hH2, hH3⟩

    have hpmin : ∀ x ∈ P.carrier.support, (0 : ℤ) ≤ p x := by
      intro x hx
      dsimp [p]
      exact_mod_cast Nat.zero_le (x 1)
    have hbase : ∃ x ∈ P.carrier.support, p x = 0 := by
      refine ⟨C.ray.outsideExponent, hLmem, ?_⟩
      dsimp [p]
      exact_mod_cast hL1
    have hexit : ∃ x ∈ P.carrier.support, (0 : ℤ) < p x := by
      refine ⟨F.highest.e1, hHmem, ?_⟩
      dsimp [p]
      rw [hH1]
      have hn1 : 1 < F.highest.n :=
        lt_of_lt_of_le Nat.one_lt_two F.highest.n_two_le
      exact_mod_cast (Nat.sub_pos_of_lt hn1)

    rcases HC4.Newton.exists_exposed_ratio_wall_from_min_fiber
        P.carrier.support p s 0 hpmin hbase hexit with
      ⟨b, a, hbS, hbp, _hbmax, haS, hap, hface, _hbG, _haG⟩

    have hb1 : b 1 = 0 := by
      dsimp [p] at hbp
      exact_mod_cast hbp
    have hb3pos : 0 < b 3 := by
      have hb3ne : b 3 ≠ 0 := by
        intro hb30
        exact hcentral ⟨b, hbS, hb1, hb30⟩
      exact Nat.pos_of_ne_zero hb3ne
    have ha1pos : 0 < a 1 := by
      dsimp [p] at hap
      exact_mod_cast hap

    have hboundZ :
        ∀ x ∈ P.carrier.support,
          (a 1 : ℤ) * (b 3 : ℤ) ≤
            ((b 3 : ℤ) - (a 3 : ℤ)) * (x 1 : ℤ) +
              (a 1 : ℤ) * (x 3 : ℤ) := by
      intro x hx
      have hw := hface.weight_le (by simpa using hx)
      dsimp [p, s, HC4.Newton.ratioWallWeight] at hw
      nlinarith [hw]

    have hH1pos : 0 < F.highest.e1 1 := by
      rw [hH1]
      have hn1 : 1 < F.highest.n :=
        lt_of_lt_of_le Nat.one_lt_two F.highest.n_two_le
      exact Nat.sub_pos_of_lt hn1
    have hb3Zpos : (0 : ℤ) < (b 3 : ℤ) := by exact_mod_cast hb3pos
    have ha1Zpos : (0 : ℤ) < (a 1 : ℤ) := by exact_mod_cast ha1pos
    have hH1Zpos : (0 : ℤ) < (F.highest.e1 1 : ℤ) := by
      exact_mod_cast hH1pos
    have hboundH := hboundZ F.highest.e1 hHmem
    rw [hH3] at hboundH
    simp only [Nat.cast_zero, mul_zero, add_zero] at hboundH

    have ha3lt : a 3 < b 3 := by
      by_contra hnot
      have hleNat : b 3 ≤ a 3 := Nat.le_of_not_gt hnot
      have hleZ : (b 3 : ℤ) ≤ (a 3 : ℤ) := by exact_mod_cast hleNat
      have hdiffNonpos : (b 3 : ℤ) - (a 3 : ℤ) ≤ 0 := sub_nonpos.mpr hleZ
      have hprodNonpos :
          ((b 3 : ℤ) - (a 3 : ℤ)) * (F.highest.e1 1 : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hdiffNonpos (le_of_lt hH1Zpos)
      have hlhsPos : (0 : ℤ) < (a 1 : ℤ) * (b 3 : ℤ) :=
        mul_pos ha1Zpos hb3Zpos
      nlinarith [hboundH]

    exact ⟨{
      lo := b
      edge := a
      lo_mem := hbS
      edge_mem := haS
      lo_one_zero := hb1
      lo_three_pos := hb3pos
      edge_one_pos := ha1pos
      edge_three_lt := ha3lt
      lower_bound := hboundZ
    }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
