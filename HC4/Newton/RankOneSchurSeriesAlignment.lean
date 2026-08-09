import HC4.Newton.GeneralFourBlockSchur
import HC4.Newton.FirstSchurLayerLinearization
import HC4.Newton.BinaryPivotGeometry
import Mathlib.Tactic

/-!
# Constant alignment of a rank-one binary Schur series

A rigid Smith packet gives a nonzero determinant-zero constant binary block,
but its kernel need not already be a coordinate axis.  This file performs
the needed constant congruence directly on the three polynomial Schur
entries, without changing the ambient family.

For a left pivot `q = [[a,b],[b,c]]`, use the constant basis

    e = (1,0),      k = (-b,a).

The transformed series entries are

    A' = A,
    B' = -b A + a B,
    C' = b^2 A - 2ab B + a^2 C.

The determinant scales by `a^2`, and the determinant-zero relation
`a*c=b^2` makes the transformed constant term exactly `diag(a,0)`.

For the right-axis pivot, swapping the two axes already gives the same
normal form with leading entry `c`.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

/-- Package three polynomial entries before rank-one alignment. -/
structure BinarySchurPolynomialSeries (R : Type*) [CommRing R] where
  active : Polynomial R
  offDiag : Polynomial R
  kernel : Polynomial R

namespace BinarySchurPolynomialSeries

/-- Binary determinant of an unaligned polynomial Schur series. -/
def determinant (S : BinarySchurPolynomialSeries R) : Polynomial R :=
  S.active * S.kernel - S.offDiag * S.offDiag

/-- Constant binary block of the series. -/
def constantBlock (S : BinarySchurPolynomialSeries R) : BinarySchurBlock R where
  a := S.active.coeff 0
  b := S.offDiag.coeff 0
  c := S.kernel.coeff 0

/-- Ring-level left-pivot certificate for the constant coefficient block.
Unlike `BinarySchurBlock.LeftPivot`, this carries no field assumption and is
therefore usable when `R` itself is a polynomial ring. -/
def LeftPivot (S : BinarySchurPolynomialSeries R) : Prop :=
  S.active.coeff 0 ≠ 0 ∧
    S.active.coeff 0 * S.kernel.coeff 0 =
      S.offDiag.coeff 0 * S.offDiag.coeff 0

/-- Ring-level pure right-axis pivot certificate. -/
def RightAxisPivot (S : BinarySchurPolynomialSeries R) : Prop :=
  S.active.coeff 0 = 0 ∧
    S.offDiag.coeff 0 = 0 ∧
    S.kernel.coeff 0 ≠ 0

/-- The left-pivot constant congruence, packaged as a canonical
`RankOneSchurSeries`. -/
noncomputable def alignLeft
    (S : BinarySchurPolynomialSeries R)
    (hleft : S.LeftPivot) :
    RankOneSchurSeries R where
  leading := S.active.coeff 0
  active := S.active
  offDiag :=
    -(Polynomial.C (S.offDiag.coeff 0)) * S.active +
      Polynomial.C (S.active.coeff 0) * S.offDiag
  kernel :=
    (Polynomial.C (S.offDiag.coeff 0)) ^ 2 * S.active -
      2 * Polynomial.C (S.active.coeff 0) *
        Polynomial.C (S.offDiag.coeff 0) * S.offDiag +
      (Polynomial.C (S.active.coeff 0)) ^ 2 * S.kernel
  active_coeff_zero := rfl
  offDiag_coeff_zero := by
    simp
    ring
  kernel_coeff_zero := by
    rcases hleft with ⟨_ha, hdet⟩
    simp [pow_two]
    calc
      S.offDiag.coeff 0 * S.offDiag.coeff 0 * S.active.coeff 0 -
          2 * S.active.coeff 0 * S.offDiag.coeff 0 * S.offDiag.coeff 0 +
          S.active.coeff 0 * S.active.coeff 0 * S.kernel.coeff 0 =
        S.active.coeff 0 *
          (S.active.coeff 0 * S.kernel.coeff 0 -
            S.offDiag.coeff 0 * S.offDiag.coeff 0) := by
              ring
      _ = 0 := by
        rw [hdet]
        ring

/-- Determinant scaling under the left-pivot congruence. -/
theorem alignLeft_determinant
    (S : BinarySchurPolynomialSeries R)
    (hleft : S.LeftPivot) :
    (S.alignLeft hleft).determinant =
      (Polynomial.C (S.active.coeff 0))^2 * S.determinant := by
  unfold alignLeft RankOneSchurSeries.determinant determinant
  ring

/-- The left-aligned leading entry is nonzero. -/
theorem alignLeft_leading_ne_zero
    (S : BinarySchurPolynomialSeries R)
    (hleft : S.LeftPivot) :
    (S.alignLeft hleft).leading ≠ 0 := by
  exact hleft.1

/-- The right-axis case is aligned just by swapping the two diagonal axes. -/
noncomputable def alignRight
    (S : BinarySchurPolynomialSeries R)
    (hright : S.RightAxisPivot) :
    RankOneSchurSeries R where
  leading := S.kernel.coeff 0
  active := S.kernel
  offDiag := S.offDiag
  kernel := S.active
  active_coeff_zero := rfl
  offDiag_coeff_zero := by
    exact hright.2.1
  kernel_coeff_zero := by
    exact hright.1

/-- Axis swap leaves the binary determinant unchanged. -/
theorem alignRight_determinant
    (S : BinarySchurPolynomialSeries R)
    (hright : S.RightAxisPivot) :
    (S.alignRight hright).determinant = S.determinant := by
  unfold alignRight RankOneSchurSeries.determinant determinant
  ring

/-- The right-aligned leading entry is nonzero. -/
theorem alignRight_leading_ne_zero
    (S : BinarySchurPolynomialSeries R)
    (hright : S.RightAxisPivot) :
    (S.alignRight hright).leading ≠ 0 := by
  exact hright.2.2

end BinarySchurPolynomialSeries

/-! ## General four-block series -/

namespace GeneralFourBlock

/-- The raw denominator-cleared binary Schur series of a polynomial
four-block. -/
def polynomialSchurSeries
    (H : GeneralFourBlock (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := H.schurA
  offDiag := H.schurB
  kernel := H.schurC

/-- Its binary determinant is exactly the general four-block cleared Schur
determinant. -/
theorem polynomialSchurSeries_determinant
    (H : GeneralFourBlock (Polynomial R)) :
    H.polynomialSchurSeries.determinant =
      H.activeDet * H.determinantCore := by
  simpa [polynomialSchurSeries, BinarySchurPolynomialSeries.determinant,
    schurDetCore] using
    H.schurDetCore_eq_activeDet_mul_determinantCore

end GeneralFourBlock

end

end HC4.Newton
