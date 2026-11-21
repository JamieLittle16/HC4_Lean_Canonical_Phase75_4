import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# Full determinant covariance for a general symmetric four-block

The denominator-cleared Schur covariance used by the A19 closing argument is
already available in `GeneralFourBlockSchur`.  R18 also needs the corresponding
full four-by-four determinant identities before cancelling the active pivot.

Both operations are ordinary congruences.  Diagonal row/column scaling by
`(s₀,s₁,t₀,t₁)` multiplies the determinant by the square of the product of the
four scales, while replacing the second complementary direction by

    lam * v + mu * u + alpha * e₀ + beta * e₁

multiplies it by `lam²`.  These are polynomial identities over an arbitrary
commutative ring; no invertibility or localization is used.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

namespace GeneralFourBlock

/-- Full determinant covariance under diagonal congruence. -/
@[simp]
theorem determinantCore_diagonalScale
    (H : GeneralFourBlock R) (s0 s1 t0 t1 : R) :
    (H.diagonalScale s0 s1 t0 t1).determinantCore =
      (s0 * s1) ^ 2 * (t0 * t1) ^ 2 * H.determinantCore := by
  unfold diagonalScale determinantCore
  ring

/-- Full determinant covariance under the second-complement shear.  Active-span
additions and additions of the first complementary direction have determinant
one; only the genuine second-quotient coefficient `lam` contributes. -/
@[simp]
theorem determinantCore_shearSecondComplement
    (H : GeneralFourBlock R) (lam mu alpha beta : R) :
    (H.shearSecondComplement lam mu alpha beta).determinantCore =
      lam ^ 2 * H.determinantCore := by
  unfold shearSecondComplement determinantCore
  ring

end GeneralFourBlock

end

end HC4.Newton
