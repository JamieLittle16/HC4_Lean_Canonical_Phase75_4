import HC4.Newton.RankOneThreeToBinarySchur
import HC4.Newton.RankOneThreeSchur
import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# Nested 1+3 then 1+2 Schur identities for a four-block

For a symmetric four-block, first clear a scalar 1+3 Schur complement and
then clear a scalar 1+2 Schur complement inside the resulting 3x3 matrix.

When the two scalar pivots are exactly the original active coordinate pair,
the nested binary entries are simply the ordinary denominator-cleared 2+2
Schur entries multiplied by the first scalar pivot.

For first pivot `a`:

    nested.active  = a * schurA
    nested.offDiag = a * schurB
    nested.kernel  = a * schurC.

For first pivot `d` and then the remaining original active coordinate, the
same identities hold with factor `d`.

These are finite polynomial identities over an arbitrary commutative ring.
They provide the lossless provenance bridge needed by the final HC4 nested
Schur seam: a nonzero nested Schur polynomial cannot be an artefact of the
auxiliary quotient.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

namespace GeneralFourBlock

/-- First pivot `a`, then the original coordinate-1 pivot: nested active
entry equals `a * schurA`. -/
theorem threePivot0_rankOneClearedThreeSchurMatrix_active
    (H : GeneralFourBlock (Polynomial R)) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrix).active =
      H.a * H.schurA := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrix,
    schurA, activeDet]
  ring

/-- First pivot `a`, then the original coordinate-1 pivot: nested
off-diagonal entry equals `a * schurB`. -/
theorem threePivot0_rankOneClearedThreeSchurMatrix_offDiag
    (H : GeneralFourBlock (Polynomial R)) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrix).offDiag =
      H.a * H.schurB := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrix,
    schurB, activeDet]
  ring

/-- First pivot `a`, then the original coordinate-1 pivot: nested kernel
entry equals `a * schurC`. -/
theorem threePivot0_rankOneClearedThreeSchurMatrix_kernel
    (H : GeneralFourBlock (Polynomial R)) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrix).kernel =
      H.a * H.schurC := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrix,
    schurC, activeDet]
  ring

/-- First pivot `d`, then the remaining original coordinate-0 pivot: nested
active entry equals `d * schurA`. -/
theorem threePivot0_rankOneClearedThreeSchurMatrixD_active
    (H : GeneralFourBlock (Polynomial R)) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrixD).active =
      H.d * H.schurA := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrixD,
    schurA, activeDet]
  ring

/-- First pivot `d`, then the remaining original coordinate-0 pivot: nested
off-diagonal entry equals `d * schurB`. -/
theorem threePivot0_rankOneClearedThreeSchurMatrixD_offDiag
    (H : GeneralFourBlock (Polynomial R)) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrixD).offDiag =
      H.d * H.schurB := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrixD,
    schurB, activeDet]
  ring

/-- First pivot `d`, then the remaining original coordinate-0 pivot: nested
kernel entry equals `d * schurC`. -/
theorem threePivot0_rankOneClearedThreeSchurMatrixD_kernel
    (H : GeneralFourBlock (Polynomial R)) :
    (threePivot0BinarySchurSeries H.rankOneClearedThreeSchurMatrixD).kernel =
      H.d * H.schurC := by
  simp [threePivot0BinarySchurSeries, rankOneClearedThreeSchurMatrixD,
    schurC, activeDet]
  ring

end GeneralFourBlock

end

end HC4.Newton
