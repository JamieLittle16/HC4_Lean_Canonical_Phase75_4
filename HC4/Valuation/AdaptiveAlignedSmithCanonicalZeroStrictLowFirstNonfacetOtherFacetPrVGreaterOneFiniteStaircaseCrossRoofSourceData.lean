import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofExposure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import Mathlib.Tactic

/-!
# Source-honest exposed cross-roof endpoint data

The lower-hull face now has one actual source point on each coordinate roof.
This file converts those literal exponents into the staircase notation consumed
by the state-free cross-roof terminal theorems.

No support is reconstructed.  Both endpoints remain literal monomials of the
same exact singular initial face.
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

/-- Literal endpoint package for one exposed cross-roof face. -/
structure QsOtherFacetPrLeftVExposedCrossRoofData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) where
  hull : QsOtherFacetPrLeftVLowerHullData F
  hi : Fin 4 →₀ ℕ
  hi_mem_face : hi ∈ hull.face.support
  hi_two_zero : hi 2 = 0
  kLo : ℕ
  jLo : ℕ
  kHi : ℕ
  jHi : ℕ
  q : ℕ
  v : ℕ
  lo_zero : hull.lo 0 = kLo
  lo_two : hull.lo 2 = q
  lo_three : hull.lo 3 = F.V * jLo
  hi_zero : hi 0 = jHi + 1
  hi_one : hi 1 = v
  hi_three : hi 3 = F.V * (kHi - 1)
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

namespace QsOtherFacetPrLeftVLowerHullData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}

/-- Package the two literal roof endpoints of the exact lower-hull face in
finite-staircase coordinates. -/
theorem exposedCrossRoofData
    (D : QsOtherFacetPrLeftVLowerHullData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrLeftVExposedCrossRoofData F) := by
  classical
  rcases D.exists_zRoof_on_face hthree houtThree with
    ⟨hi, hiFace, hi2⟩
  have hiP := D.face_support_subset hiFace

  rcases F.support_staircase_classification hthree houtThree D.lo_mem with
    ⟨jLo, hloFirst, _hloPairLe, _hloJLe, _hloTop, _hloLocked⟩
  rcases F.support_staircase_classification hthree houtThree hiP with
    ⟨jHi, hhiFirst, _hhiPairLe, _hhiJLe, _hhiTop, _hhiLocked⟩

  let kLo : ℕ := D.lo 0
  let q : ℕ := D.lo 2
  let v : ℕ := hi 1
  let kHi : ℕ := hi 0 + hi 1

  have hloFirstNat : D.lo 0 + D.lo 2 = jLo + 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate,
      D.lo_one_zero] using hloFirst
  have hhiFirstNat : hi 0 = jHi + 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate, hi2] using hhiFirst

  have hkLoPos : 0 < kLo := by
    have hp := F.support_pair_pos hthree houtThree D.lo_mem
    dsimp [kLo]
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate,
      D.lo_one_zero] using hp
  have hqPos : 0 < q := by
    simpa [q] using D.lo_two_pos
  have hjLoPos : 0 < jLo := by
    dsimp [kLo, q] at hkLoPos hqPos
    omega

  have hcostHi := D.cost_eq_of_mem_face hiFace
  rw [hi2] at hcostHi
  norm_num at hcostHi
  have hvPos : 0 < v := by
    dsimp [v]
    by_contra hnot
    have hv0 : hi 1 = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hv0] at hcostHi
    norm_num at hcostHi
    rcases hcostHi with hEdgeZero | hLoTwoZero
    · exact (Nat.ne_of_gt D.edge_one_pos) hEdgeZero
    · exact (Nat.ne_of_gt D.lo_two_pos) hLoTwoZero

  have hkHiPos : 0 < kHi := by
    dsimp [kHi]
    omega
  have hhiRoof : jHi + 1 < kHi := by
    dsimp [kHi, v] at hvPos ⊢
    rw [hhiFirstNat]
    omega
  have hloRoof : kLo < jLo + 1 := by
    dsimp [kLo, q] at hkLoPos hqPos ⊢
    omega

  have hwallLoRaw := F.support_deficit_wall hthree houtThree D.lo_mem
  have hwallLo :
      ((F.highest.n : ℤ) - 1) * (jLo : ℤ) =
        (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - (kLo : ℤ)) := by
    have hfirstSumZ :
        (D.lo 0 : ℤ) + (D.lo 2 : ℤ) = (jLo : ℤ) + 1 := by
      exact_mod_cast hloFirstNat
    have hfirstZ :
        (D.lo 0 : ℤ) + (D.lo 2 : ℤ) - 1 = (jLo : ℤ) := by
      linarith only [hfirstSumZ]
    rw [D.lo_one_zero] at hwallLoRaw
    norm_num at hwallLoRaw
    rw [hfirstZ] at hwallLoRaw
    simpa [kLo] using hwallLoRaw

  have hwallHiRaw := F.support_deficit_wall hthree houtThree hiP
  have hwallHi :
      ((F.highest.n : ℤ) - 1) * (jHi : ℤ) =
        (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - (kHi : ℤ)) := by
    have hhi0Z : (hi 0 : ℤ) = (jHi : ℤ) + 1 := by
      exact_mod_cast hhiFirstNat
    have hkHiZ : (kHi : ℤ) = (hi 0 : ℤ) + (hi 1 : ℤ) := by
      dsimp [kHi]
    have hleft : (hi 0 : ℤ) - 1 = (jHi : ℤ) := by
      linarith only [hhi0Z]
    have hright :
        (F.highest.n : ℤ) - (hi 0 : ℤ) - (hi 1 : ℤ) =
          (F.highest.n : ℤ) - (kHi : ℤ) := by
      linarith only [hkHiZ]
    rw [hi2] at hwallHiRaw
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
    rw [hhiFirstNat]
    omega

  have hloThree : D.lo 3 = F.V * jLo := by
    have hs := (F.support_staircase_equations hthree houtThree D.lo_mem).2
    simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
      HC4.Polynomial.rankThreeQuotientCoordinate_pair,
      HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
      one_mul] at hs
    push_cast at hs
    have hfirstZ :
        (D.lo 0 : ℤ) + (D.lo 2 : ℤ) = (jLo : ℤ) + 1 := by
      exact_mod_cast hloFirstNat
    rw [D.lo_one_zero] at hs
    norm_num at hs
    have hthreeZ :
        (D.lo 3 : ℤ) = (F.V : ℤ) * (jLo : ℤ) := by
      linear_combination hs + (F.V : ℤ) * hfirstZ
    exact_mod_cast hthreeZ

  have hhiThree : hi 3 = F.V * (kHi - 1) := by
    have hs := (F.support_staircase_equations hthree houtThree hiP).2
    simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
      HC4.Polynomial.rankThreeQuotientCoordinate_pair,
      HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
      one_mul] at hs
    push_cast at hs
    have hkHiZ : (kHi : ℤ) = (hi 0 : ℤ) + (hi 1 : ℤ) := by
      dsimp [kHi]
    have hkHiOne : 1 ≤ kHi := by omega
    have hsubCast : ((kHi - 1 : ℕ) : ℤ) = (kHi : ℤ) - 1 := by
      rw [Nat.cast_sub hkHiOne]
      norm_num
    rw [hi2] at hs
    norm_num at hs
    have hthreeLinear :
        (hi 3 : ℤ) = (F.V : ℤ) * ((kHi : ℤ) - 1) := by
      linear_combination hs - (F.V : ℤ) * hkHiZ
    have hthreeZ : (hi 3 : ℤ) = ((F.V * (kHi - 1) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, hsubCast]
      exact hthreeLinear
    exact_mod_cast hthreeZ

  exact ⟨{
    hull := D
    hi := hi
    hi_mem_face := hiFace
    hi_two_zero := hi2
    kLo := kLo
    jLo := jLo
    kHi := kHi
    jHi := jHi
    q := q
    v := v
    lo_zero := rfl
    lo_two := rfl
    lo_three := hloThree
    hi_zero := hhiFirstNat
    hi_one := rfl
    hi_three := hhiThree
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

end QsOtherFacetPrLeftVLowerHullData

/-- Whole-carrier transition: either a central roof-intersection monomial is
present, or the actual source has an exposed cross-roof face with fully
packaged staircase endpoints. -/
theorem QsOtherFacetPrLeftVContactFrontierData.central_or_exposedCrossRoof
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∃ e ∈ P.carrier.support, e 1 = 0 ∧ e 2 = 0) ∨
      Nonempty (QsOtherFacetPrLeftVExposedCrossRoofData F) := by
  rcases F.central_or_lowerHull hthree houtThree with hcentral | hD
  · exact Or.inl hcentral
  · rcases hD with ⟨D⟩
    exact Or.inr (D.exposedCrossRoofData hthree houtThree)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
