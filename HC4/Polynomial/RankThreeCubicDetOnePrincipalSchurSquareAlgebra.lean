import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# A determinant-one 2+2 symmetric Schur chart with zero final diagonal

For a general symmetric four-block H, the existing exact cleared
Schur determinant identity gives

  schurA * schurC - schurB^2 = activeDet * determinantCore.

When the transverse 3x3 block is singular, the complementary
transverse Schur diagonal becomes schurC = 0. If the full
Hessian determinant equals one, then

  schurB^2 = -activeDet.

This is an exact identity over any commutative ring. It does
not use a square root or an algebraically closed base field.

The future source-level step is to identify the actual quadratic
principal pivot and its mixed longitudinal pair with these chart
entries. These lemmas by themselves do not assert that identification.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton
noncomputable section

variable {R : Type*} [CommRing R]

/-- In a determinant-one symmetric 2+2 block with vanishing
last cleared Schur diagonal, the square of the remaining
Schur coupling is exactly minus the active principal minor. -/
theorem detOne_principalSchur_lastZero_couplingSquare
    (H : GeneralFourBlock R)
    (hdet : H.determinantCore = 1)
    (hzero : H.schurC = 0) :
    H.schurB ^ 2 = -H.activeDet := by
  have h := H.schurDetCore_eq_activeDet_mul_determinantCore
  change H.schurA * H.schurC - H.schurB * H.schurB =
    H.activeDet * H.determinantCore at h
  have hneg : -(H.schurB * H.schurB) = H.activeDet := by
    simpa [hzero, hdet] using h
  calc
    H.schurB ^ 2 = - (-(H.schurB * H.schurB)) := by ring
    _ = -H.activeDet := by rw [hneg]

/-- A nonzero original principal two-by-two minor therefore
forces nonzero mixed coupling in its rank-two det-one Schur chart. -/
theorem detOne_principalSchur_lastZero_coupling_ne_zero
    (H : GeneralFourBlock R)
    (hdet : H.determinantCore = 1)
    (hzero : H.schurC = 0)
    (hpivot : H.activeDet ≠ 0) :
    H.schurB ≠ 0 := by
  intro hb
  have hsq := detOne_principalSchur_lastZero_couplingSquare
    H hdet hzero
  have hδ : H.activeDet = 0 := by
    simpa [hb] using hsq.symm
  exact hpivot hδ

end
end HC4.Polynomial.RankThreeCubic
