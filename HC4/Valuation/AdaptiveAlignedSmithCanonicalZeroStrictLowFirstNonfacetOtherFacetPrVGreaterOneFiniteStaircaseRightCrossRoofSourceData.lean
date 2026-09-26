import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCrossRoofExposure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import Mathlib.Tactic

/-!
# Source-honest mirrored exposed cross-roof endpoint data

The mirrored lower-hull face contains literal source points on `e₁=0` and
`e₃=0`.  We package them in the same staircase integers
`(kLo,jLo,kHi,jHi,q,v)` used by the state-free mirror terminal theorem.  The
arithmetic is unchanged; only source coordinates `2` and `3` are swapped.
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

structure QsOtherFacetPrRightVExposedCrossRoofData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) where
  hull : QsOtherFacetPrRightVLowerHullData F
  hi : Fin 4 →₀ ℕ
  hi_mem_face : hi ∈ hull.face.support
  hi_three_zero : hi 3 = 0
  kLo : ℕ
  jLo : ℕ
  kHi : ℕ
  jHi : ℕ
  q : ℕ
  v : ℕ
  lo_zero : hull.lo 0 = kLo
  lo_three : hull.lo 3 = q
  lo_two : hull.lo 2 = F.V * jLo
  hi_zero : hi 0 = jHi + 1
  hi_one : hi 1 = v
  hi_two : hi 2 = F.V * (kHi - 1)
  kLo_pos : 0 < kLo
  jLo_pos : 0 < jLo
  q_pos : 0 < q
  v_pos : 0 < v
  pair_lt : kLo < kHi
  q_eq : q = jLo + 1 - kLo
  v_eq : v = kHi - jHi - 1
  wall_lo :
    ((F.highest.n : ℤ) - 1) * (jLo : ℤ) =
      (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - (kLo : ℤ))
  wall_hi :
    ((F.highest.n : ℤ) - 1) * (jHi : ℤ) =
      (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - (kHi : ℤ))

namespace QsOtherFacetPrRightVLowerHullData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrRightVContactFrontierData C P S R}

/-- Package the two literal roof endpoints of the mirrored exact face. -/
theorem exposedCrossRoofData
    (D : QsOtherFacetPrRightVLowerHullData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrRightVExposedCrossRoofData F) := by
  classical
  rcases D.exists_wRoof_on_face hthree houtThree with
    ⟨hi, hiFace, hi3⟩
  have hiP := D.face_support_subset hiFace

  rcases F.support_staircase_classification hthree houtThree D.lo_mem with
    ⟨jLo, hloSecond, _hloPairLe, _hloJLe, _hloTop, _hloLocked⟩
  rcases F.support_staircase_classification hthree houtThree hiP with
    ⟨jHi, hhiSecond, _hhiPairLe, _hhiJLe, _hhiTop, _hhiLocked⟩

  let kLo : ℕ := D.lo 0
  let q : ℕ := D.lo 3
  let v : ℕ := hi 1
  let kHi : ℕ := hi 0 + hi 1

  have hloSecondNat : D.lo 0 + D.lo 3 = jLo + 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate,
      D.lo_one_zero] using hloSecond
  have hhiSecondNat : hi 0 = jHi + 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate, hi3] using hhiSecond

  have hkLoPos : 0 < kLo := by
    have hp := F.support_pair_pos hthree houtThree D.lo_mem
    dsimp [kLo]
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate,
      D.lo_one_zero] using hp
  have hqPos : 0 < q := by
    simpa [q] using D.lo_three_pos
  have hjLoPos : 0 < jLo := by
    dsimp [kLo, q] at hkLoPos hqPos
    omega

  have hcostHi := D.cost_eq_of_mem_face hiFace
  rw [hi3] at hcostHi
  norm_num at hcostHi
  have hvPos : 0 < v := by
    dsimp [v]
    by_contra hnot
    have hv0 : hi 1 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hv0] at hcostHi
    norm_num at hcostHi
    rcases hcostHi with hEdgeZero | hLoThreeZero
    · exact (Nat.ne_of_gt D.edge_one_pos) hEdgeZero
    · exact (Nat.ne_of_gt D.lo_three_pos) hLoThreeZero

  have hhiRoof : jHi + 1 < kHi := by
    dsimp [kHi, v] at hvPos ⊢
    rw [hhiSecondNat]
    omega
  have hloRoof : kLo < jLo + 1 := by
    dsimp [kLo, q] at hkLoPos hqPos ⊢
    omega

  have hwallLoRaw := F.support_deficit_wall hthree houtThree D.lo_mem
  have hwallLo :
      ((F.highest.n : ℤ) - 1) * (jLo : ℤ) =
        (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - (kLo : ℤ)) := by
    have hsecondSumZ :
        (D.lo 0 : ℤ) + (D.lo 3 : ℤ) = (jLo : ℤ) + 1 := by
      exact_mod_cast hloSecondNat
    have hsecondZ :
        (D.lo 0 : ℤ) + (D.lo 3 : ℤ) - 1 = (jLo : ℤ) := by
      linarith only [hsecondSumZ]
    rw [D.lo_one_zero] at hwallLoRaw
    norm_num at hwallLoRaw
    rw [hsecondZ] at hwallLoRaw
    simpa [kLo] using hwallLoRaw

  have hwallHiRaw := F.support_deficit_wall hthree houtThree hiP
  have hwallHi :
      ((F.highest.n : ℤ) - 1) * (jHi : ℤ) =
        (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - (kHi : ℤ)) := by
    have hhi0Z : (hi 0 : ℤ) = (jHi : ℤ) + 1 := by
      exact_mod_cast hhiSecondNat
    have hkHiZ : (kHi : ℤ) = (hi 0 : ℤ) + (hi 1 : ℤ) := by
      dsimp [kHi]
    have hleft : (hi 0 : ℤ) - 1 = (jHi : ℤ) := by
      linarith only [hhi0Z]
    have hright :
        (F.highest.n : ℤ) - (hi 0 : ℤ) - (hi 1 : ℤ) =
          (F.highest.n : ℤ) - (kHi : ℤ) := by
      linarith only [hkHiZ]
    rw [hi3] at hwallHiRaw
    norm_num at hwallHiRaw
    rw [hleft, hright] at hwallHiRaw
    exact hwallHiRaw

  have hklt : kLo < kHi :=
    HC4.Polynomial.crossRoof_pair_lt_of_roof_signs
      F.highest.n_two_le F.locked.ell_pos
      hwallLo hwallHi hloRoof hhiRoof

  have hqEq : q = jLo + 1 - kLo := by
    dsimp [q, kLo]
    omega
  have hvEq : v = kHi - jHi - 1 := by
    dsimp [v, kHi]
    rw [hhiSecondNat]
    omega

  have hloTwo : D.lo 2 = F.V * jLo := by
    have hs := (F.support_staircase_equations hthree houtThree D.lo_mem).2
    simp only [HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
      HC4.Polynomial.rankThreeQuotientCoordinate_pair,
      HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
      one_mul] at hs
    push_cast at hs
    have hsecondZ :
        (D.lo 0 : ℤ) + (D.lo 3 : ℤ) = (jLo : ℤ) + 1 := by
      exact_mod_cast hloSecondNat
    rw [D.lo_one_zero] at hs
    norm_num at hs
    have htwoZ :
        (D.lo 2 : ℤ) = (F.V : ℤ) * (jLo : ℤ) := by
      linear_combination hs + (F.V : ℤ) * hsecondZ
    exact_mod_cast htwoZ

  have hhiTwo : hi 2 = F.V * (kHi - 1) := by
    have hs := (F.support_staircase_equations hthree houtThree hiP).2
    simp only [HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
      HC4.Polynomial.rankThreeQuotientCoordinate_pair,
      HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
      one_mul] at hs
    push_cast at hs
    have hkHiZ : (kHi : ℤ) = (hi 0 : ℤ) + (hi 1 : ℤ) := by
      dsimp [kHi]
    have hkHiOne : 1 ≤ kHi := by omega
    have hsubCast : ((kHi - 1 : ℕ) : ℤ) = (kHi : ℤ) - 1 := by
      rw [Nat.cast_sub hkHiOne]
      norm_num
    rw [hi3] at hs
    norm_num at hs
    have htwoLinear :
        (hi 2 : ℤ) = (F.V : ℤ) * ((kHi : ℤ) - 1) := by
      linear_combination hs - (F.V : ℤ) * hkHiZ
    have htwoZ : (hi 2 : ℤ) = ((F.V * (kHi - 1) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, hsubCast]
      exact htwoLinear
    exact_mod_cast htwoZ

  exact ⟨{
    hull := D
    hi := hi
    hi_mem_face := hiFace
    hi_three_zero := hi3
    kLo := kLo
    jLo := jLo
    kHi := kHi
    jHi := jHi
    q := q
    v := v
    lo_zero := rfl
    lo_three := rfl
    lo_two := hloTwo
    hi_zero := hhiSecondNat
    hi_one := rfl
    hi_two := hhiTwo
    kLo_pos := hkLoPos
    jLo_pos := hjLoPos
    q_pos := hqPos
    v_pos := hvPos
    pair_lt := hklt
    q_eq := hqEq
    v_eq := hvEq
    wall_lo := hwallLo
    wall_hi := hwallHi
  }⟩

end QsOtherFacetPrRightVLowerHullData

/-- Whole-carrier mirrored transition: central source monomial or exposed
cross-roof face with fully packaged staircase endpoints. -/
theorem QsOtherFacetPrRightVContactFrontierData.central_or_exposedCrossRoof
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ e ∈ P.carrier.support, e 1 = 0 ∧ e 3 = 0) ∨
      Nonempty (QsOtherFacetPrRightVExposedCrossRoofData F) := by
  rcases F.central_or_lowerHull hthree houtThree with hcentral | hD
  · exact Or.inl hcentral
  · rcases hD with ⟨D⟩
    exact Or.inr (D.exposedCrossRoofData hthree houtThree)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
