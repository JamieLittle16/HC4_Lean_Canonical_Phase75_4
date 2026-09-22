import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurLaterKernelOpening
import Mathlib.Tactic

/-!
# Transport the strictly later projected opening into the normalised 3x3 tail

The tangent branch has two physical orders:

* j: the first raw Hessian kernel-row opening;
* J: the first projected 1+3 Schur kernel-column opening, with j < J.

Let q be the common first positive order of the complete 3x3 Schur quotient.
Because the entry opening at J is one candidate for that common order,

    q <= J.

After removing the common factor X^q, the same projected kernel entry opens
at relative order J-q, and every projected kernel entry is zero below that
relative order.

This gives the decisive split:

* q <= j: then 0 < J-q, so the normalised 3x3 tail carries a genuine positive
  later kernel opening;
* j < q: then every entry of the complete raw 3x3 quotient is zero through
  order j.  Thus the first Hessian opening is fully tangent to the rank-one
  locus, not merely tangent in its projected kernel column.

No progress theorem or JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Tail-facing form of the later projected kernel opening. -/
structure ThreeSchurTangentTailKernelOpeningData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1) where
  tangent : S.ThreeSchurTangentAtFirstBreak M
  physical : S.ThreeSchurTangentLaterKernelOpeningData M
  commonOrder : ℕ
  commonOrder_eq : commonOrder = S.firstThreeSchurOrder
  common_le_later : commonOrder ≤ physical.laterOrder
  relativeOrder : ℕ
  relativeOrder_eq : relativeOrder = physical.laterOrder - commonOrder
  opens :
    (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
      S.toExactZeroThreeSchurClock.hasPositiveEntryLayer
      physical.index 2).coeff relativeOrder ≠ 0
  lower_zero :
    ∀ i : Fin 3, ∀ n : ℕ, n < relativeOrder →
      (S.toExactZeroThreeSchurClock.zeroSeries.tailMatrix
        S.toExactZeroThreeSchurClock.hasPositiveEntryLayer i 2).coeff n = 0

/-- The common 3x3 first order is no later than the retained later kernel
opening. -/
theorem ThreeSchurTangentLaterKernelOpeningData.firstThreeSchurOrder_le_later
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentLaterKernelOpeningData M) :
    S.firstThreeSchurOrder ≤ D.laterOrder := by
  let E := S.toExactZeroThreeSchurClock
  have hJpos : 0 < D.laterOrder := by
    exact lt_trans M.mixed.layer.order_pos D.first_lt_later
  have hcand : E.zeroSeries.HasPositiveEntryLayer :=
    ⟨D.laterOrder, hJpos, D.index, 2, D.opens⟩
  have hmin :
      E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer ≤
        D.laterOrder := by
    unfold ZeroThreeSchurSeries.firstPositiveEntryOrder
    exact Nat.find_min' E.hasPositiveEntryLayer hcand
  simpa [TopKernelThreeSchurClockData.firstThreeSchurOrder, E] using hmin

/-- Divide the strict physical opening by the common first 3x3 factor. -/
theorem ThreeSchurTangentLaterKernelOpeningData.toTailKernelOpeningData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentLaterKernelOpeningData M) :
    Nonempty (S.ThreeSchurTangentTailKernelOpeningData M) := by
  let E := S.toExactZeroThreeSchurClock
  let q := S.firstThreeSchurOrder
  let J := D.laterOrder
  let r := J - q
  have hqJ : q ≤ J := by
    simpa [q, J] using D.firstThreeSchurOrder_le_later
  have hadd : q + r = J := by
    dsimp [r]
    exact Nat.add_sub_of_le hqJ

  have hopen : (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer
      D.index 2).coeff r ≠ 0 := by
    have ht :=
      E.zeroSeries.entry_coeff_first_add_eq_tail
        E.hasPositiveEntryLayer D.index 2 r
    have hfirst :
        E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer = q := by
      rfl
    rw [hfirst, hadd] at ht
    intro hz
    apply D.opens
    rw [ht]
    exact hz

  have hlower :
      ∀ i : Fin 3, ∀ n : ℕ, n < r →
        (E.zeroSeries.tailMatrix E.hasPositiveEntryLayer i 2).coeff n = 0 := by
    intro i n hn
    have hphys : q + n < J := by
      dsimp [r] at hn
      omega
    have hraw := D.lower_zero i (q + n) hphys
    have ht :=
      E.zeroSeries.entry_coeff_first_add_eq_tail
        E.hasPositiveEntryLayer i 2 n
    have hfirst :
        E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer = q := by
      rfl
    rw [hfirst] at ht
    rw [← ht]
    exact hraw

  exact ⟨{
    tangent := D.tangent
    physical := D
    commonOrder := q
    commonOrder_eq := rfl
    common_le_later := hqJ
    relativeOrder := r
    relativeOrder_eq := rfl
    opens := hopen
    lower_zero := hlower
  }⟩

/-- If the common 3x3 quotient already opens no later than the first raw
kernel-row break, then the normalised tail kernel opening is strictly
positive. -/
theorem ThreeSchurTangentTailKernelOpeningData.relativeOrder_pos_of_common_le_firstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : S.ThreeSchurTangentTailKernelOpeningData M)
    (hle : D.commonOrder ≤ M.mixed.layer.order) :
    0 < D.relativeOrder := by
  rw [D.relativeOrder_eq]
  omega

/-- The alternative q>j means the complete raw 3x3 Schur quotient is zero
through the physical first Hessian break. -/
structure ThreeSchurFullyTangentAtFirstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Prop where
  first_lt_common :
    M.mixed.layer.order < S.firstThreeSchurOrder
  quotient_zero_through :
    ∀ i r : Fin 3, ∀ n : ℕ, n ≤ M.mixed.layer.order →
      (S.toExactZeroThreeSchurClock.zeroSeries.matrix i r).coeff n = 0

/-- If the common 3x3 order lies after j, full tangency through j is automatic
from minimality of the common first entry order. -/
theorem fullyTangentAtFirstBreak_of_first_lt_common
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (hlt : M.mixed.layer.order < S.firstThreeSchurOrder) :
    S.ThreeSchurFullyTangentAtFirstBreak M := by
  refine ⟨hlt, ?_⟩
  intro i r n hn
  let E := S.toExactZeroThreeSchurClock
  have hnlt : n < E.firstOrder := by
    change n < S.firstThreeSchurOrder
    exact lt_of_le_of_lt hn hlt
  exact E.zeroSeries.entry_coeff_eq_zero_of_lt_first
    E.hasPositiveEntryLayer i r hnlt

/-- **Tangent-order dichotomy.**

A tangent first Hessian opening yields either a genuine positive projected
kernel opening in the normalised 3x3 tail, or complete 3x3 Schur tangency
through the physical first-break layer. -/
theorem ThreeSchurTangentAtFirstBreak.tailKernelOpening_or_fullyTangent
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : S.ThreeSchurTangentAtFirstBreak M) :
    (∃ D : S.ThreeSchurTangentTailKernelOpeningData M,
        0 < D.relativeOrder) ∨
      S.ThreeSchurFullyTangentAtFirstBreak M := by
  rcases R.toLaterKernelOpeningData with ⟨L⟩
  rcases L.toTailKernelOpeningData with ⟨D⟩
  by_cases hle : S.firstThreeSchurOrder ≤ M.mixed.layer.order
  · left
    refine ⟨D, ?_⟩
    apply D.relativeOrder_pos_of_common_le_firstBreak
    simpa [D.commonOrder_eq] using hle
  · right
    apply fullyTangentAtFirstBreak_of_first_lt_common
    omega

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
