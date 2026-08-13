import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingTransverseTerminalImpossible
import Mathlib.Tactic

/-!
# The only canonical terminal survivor is longitudinal

The transverse canonical terminal square has been eliminated directly by the
first-layer gap and terminal contact arithmetic.  Consequently the equality
branch `j = Delta` has only two possible outputs:

* an explicit earlier coefficient/section wall on the canonical ray; or
* the original (unsheared) longitudinal fresh square reaches canonical
  terminal first contact.

This removes the entire transverse terminal/cocharacter loop.  The remaining
terminal geometry is therefore the much more rigid longitudinal weight
`(0, 2 Delta, 2 Delta, 2 Delta)`, which is the input for the next direct
axis-structure argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The sole possible terminal survivor after transverse terminal elimination:
the original longitudinal fresh square together with its canonical terminal
first-contact fibre. -/
structure DirectClosingLongitudinalCanonicalTerminalData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) where
  fresh : C.HasFreshDirectClosingSquareAt (0 : Fin 4)
  integrality :
    DirectClosingCanonicalSquareIntegralityData
      (C.directClosingLongitudinalSquareSource fresh)
  terminal :
    Nonempty (DirectClosingSquareFirstContactTerminalData
      (integrality.toFirstContactLattice heq))

namespace DirectClosingLongitudinalCanonicalTerminalData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
variable {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}

/-- The aligned-square source of a longitudinal terminal survivor is literally
the original closing source family. -/
theorem source_family_eq
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq) :
    (C.directClosingLongitudinalSquareSource S.fresh).family = C.family := by
  rfl

/-- Its canonical source weight is the explicit longitudinal weight:
zero on coordinate `0`, `2*Delta` on each transverse coordinate. -/
theorem canonicalWeight_zero
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq) :
    directClosingCanonicalSquareWeight B.aligned.endpoint.defect
      (C.directClosingLongitudinalSquareSource S.fresh).index (0 : Fin 4) = 0 := by
  simp [directClosingLongitudinalSquareSource]

/-- Each of the three transverse coordinates has canonical weight
`2*Delta`. -/
theorem canonicalWeight_transverse
    (S : DirectClosingLongitudinalCanonicalTerminalData C heq)
    (i : Fin 4) (hi : i ≠ 0) :
    directClosingCanonicalSquareWeight B.aligned.endpoint.defect
      (C.directClosingLongitudinalSquareSource S.fresh).index i =
        2 * B.aligned.endpoint.defect := by
  simp [directClosingLongitudinalSquareSource,
    directClosingCanonicalSquareWeight, hi]

end DirectClosingLongitudinalCanonicalTerminalData

/-- **Sharp equality frontier after transverse terminal elimination.**

At `j = Delta`, either the canonical square ray hits a concrete earlier
coefficient/section wall, or its only possible terminal first-contact survivor
is the original longitudinal fresh-square source. -/
theorem directClosing_equality_earlierWall_or_longitudinalTerminal
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    (∃ D : DirectClosingAlignedSquareSourceData C,
      DirectClosingCanonicalSquareEarlierWall D) ∨
      Nonempty (DirectClosingLongitudinalCanonicalTerminalData C heq) := by
  rcases C.directClosing_freshLongitudinalSquare_or_transverseAlignedSquare heq with
    hlong | htrans
  · let D := C.directClosingLongitudinalSquareSource hlong
    rcases directClosingCanonicalSquare_terminal_or_earlierWall D heq with
      hterm | hwall
    · rcases hterm with ⟨G, hT⟩
      right
      exact ⟨{
        fresh := hlong
        integrality := G
        terminal := hT
      }⟩
    · left
      exact ⟨D, hwall⟩
  · rcases htrans with ⟨A⟩
    let D := A.toAlignedSquareSource
    rcases directClosingCanonicalSquare_terminal_or_earlierWall D heq with
      hterm | hwall
    · rcases hterm with ⟨G, hT⟩
      rcases hT with ⟨T⟩
      exact False.elim (A.canonicalTerminal_impossible heq G T)
    · left
      exact ⟨D, hwall⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
