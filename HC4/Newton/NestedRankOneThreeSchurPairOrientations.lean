import HC4.Newton.NestedRankOneThreeSchurFourBlock
import Mathlib.Tactic

/-!
# Coordinate-pair orientations for nested scalar Schur elimination

The top-kernel HC4 seam may choose any two of the three non-kernel
coordinates as its successive scalar pivots.  The first nested-Schur file
handles the active pair (0,1).  This file packages the other two coordinate
pairs by literal reordering of a general symmetric four-block:

* `pair02Block` displays coordinates [0,2,1,3];
* `pair12Block` displays coordinates [1,2,0,3].

The kernel coordinate remains last.  We then prove the remaining nested
1+3/1+2 identities directly.  Thus every possible pair of scalar pivots
produces exactly one scalar multiple of the ordinary 2+2 Schur series in the
corresponding coordinate-pair chart.

No matrix inversion or field hypothesis is used.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

namespace GeneralFourBlock

/-- Same symmetric four-block displayed in coordinate order [0,2,1,3]. -/
def pair02Block (H : GeneralFourBlock R) : GeneralFourBlock R where
  a := H.a
  b := H.p
  d := H.x
  p := H.b
  q := H.q
  r := H.r
  s := H.y
  x := H.d
  y := H.s
  z := H.z

/-- Same symmetric four-block displayed in coordinate order [1,2,0,3]. -/
def pair12Block (H : GeneralFourBlock R) : GeneralFourBlock R where
  a := H.d
  b := H.r
  d := H.x
  p := H.b
  q := H.s
  r := H.p
  s := H.y
  x := H.a
  y := H.q
  z := H.z

/-! First scalar pivot 0, second scalar pivot 2. -/

theorem threePivot1_rankOneClearedThreeSchurMatrix_active
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrix).active =
      H.a * H.pair02Block.schurA := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrix,
    pair02Block, schurA, activeDet]
  ring

theorem threePivot1_rankOneClearedThreeSchurMatrix_offDiag
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrix).offDiag =
      H.a * H.pair02Block.schurB := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrix,
    pair02Block, schurB, activeDet]
  ring

theorem threePivot1_rankOneClearedThreeSchurMatrix_kernel
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrix).kernel =
      H.a * H.pair02Block.schurC := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrix,
    pair02Block, schurC, activeDet]
  ring

/-! First scalar pivot 1, second scalar pivot 2. -/

theorem threePivot1_rankOneClearedThreeSchurMatrixD_active
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrixD).active =
      H.d * H.pair12Block.schurA := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrixD,
    pair12Block, schurA, activeDet]
  ring

theorem threePivot1_rankOneClearedThreeSchurMatrixD_offDiag
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrixD).offDiag =
      H.d * H.pair12Block.schurB := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrixD,
    pair12Block, schurB, activeDet]
  ring

theorem threePivot1_rankOneClearedThreeSchurMatrixD_kernel
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrixD).kernel =
      H.d * H.pair12Block.schurC := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrixD,
    pair12Block, schurC, activeDet]
  ring

/-! First scalar pivot 2, second scalar pivot 0. -/

theorem threePivot0_rankOneClearedThreeSchurMatrixX_active
    (H : GeneralFourBlock R) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrixX).active =
      H.x * H.pair02Block.schurA := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrixX,
    pair02Block, schurA, activeDet]
  ring

theorem threePivot0_rankOneClearedThreeSchurMatrixX_offDiag
    (H : GeneralFourBlock R) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrixX).offDiag =
      H.x * H.pair02Block.schurB := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrixX,
    pair02Block, schurB, activeDet]
  ring

theorem threePivot0_rankOneClearedThreeSchurMatrixX_kernel
    (H : GeneralFourBlock R) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrixX).kernel =
      H.x * H.pair02Block.schurC := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrixX,
    pair02Block, schurC, activeDet]
  ring

/-! First scalar pivot 2, second scalar pivot 1. -/

theorem threePivot1_rankOneClearedThreeSchurMatrixX_active
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrixX).active =
      H.x * H.pair12Block.schurA := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrixX,
    pair12Block, schurA, activeDet]
  ring

theorem threePivot1_rankOneClearedThreeSchurMatrixX_offDiag
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrixX).offDiag =
      H.x * H.pair12Block.schurB := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrixX,
    pair12Block, schurB, activeDet]
  ring

theorem threePivot1_rankOneClearedThreeSchurMatrixX_kernel
    (H : GeneralFourBlock R) :
    (threePivot1BinarySchurSeries H.rankOneClearedThreeSchurMatrixX).kernel =
      H.x * H.pair12Block.schurC := by
  simp [threePivot1BinarySchurSeries, rankOneClearedThreeSchurMatrixX,
    pair12Block, schurC, activeDet]
  ring

end GeneralFourBlock

end

end HC4.Newton
