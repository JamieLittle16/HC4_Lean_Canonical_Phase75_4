import HC4.Newton.RankOneSchurSeriesAlignment
import Mathlib.Tactic

/-!
# Tangential aligned Schur layers lie on the raw rank-one ray

`RankOneSchurSeriesAlignment` aligns the constant coefficient of a binary
Schur series by a polynomial-valued congruence.  For the source-level
closing argument we must not mistake this matrix congruence for an honest
source change.

This file records the coefficient identities that can safely be read back in
the *raw* Schur series.

For a left pivot with constant block

    [[a,b],[b,c]],      a != 0,      a*c = b^2,

the aligned transverse coefficients at order `n` are

    B'_n = -b A_n + a B_n,
    C'_n = b^2 A_n - 2ab B_n + a^2 C_n.

Hence `B'_n = C'_n = 0` implies

    a B_n = b A_n,
    a^2 C_n = b^2 A_n.

Thus the raw coefficient block at order `n` lies on the same projective
rank-one ray as the constant block, without introducing any division.

For a right-axis pivot the aligned series is just the axis swap, so
transverse tangency says `A_n = B_n = 0` directly.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

namespace BinarySchurPolynomialSeries

/-- Raw coefficient form of the aligned left-pivot off-diagonal entry. -/
theorem alignLeft_offDiag_coeff
    (S : BinarySchurPolynomialSeries R)
    (hleft : S.LeftPivot)
    (n : ℕ) :
    (S.alignLeft hleft).offDiag.coeff n =
      -(S.offDiag.coeff 0) * S.active.coeff n +
        S.active.coeff 0 * S.offDiag.coeff n := by
  simp [alignLeft, Polynomial.coeff_add, Polynomial.coeff_C_mul]

/-- Raw coefficient form of the aligned left-pivot kernel entry. -/
theorem alignLeft_kernel_coeff
    (S : BinarySchurPolynomialSeries R)
    (hleft : S.LeftPivot)
    (n : ℕ) :
    (S.alignLeft hleft).kernel.coeff n =
      (S.offDiag.coeff 0)^2 * S.active.coeff n -
        2 * S.active.coeff 0 * S.offDiag.coeff 0 * S.offDiag.coeff n +
        (S.active.coeff 0)^2 * S.kernel.coeff n := by
  simp [alignLeft, Polynomial.coeff_sub, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, pow_two, mul_two, mul_assoc]

/-- Vanishing aligned transverse coefficients force the raw coefficient to
lie on the same rank-one ray as the constant left-pivot block.  The
statement is denominator-free and therefore valid over an arbitrary
commutative coefficient ring. -/
theorem rawRayAtOrder_of_alignLeft_tangential
    (S : BinarySchurPolynomialSeries R)
    (hleft : S.LeftPivot)
    (n : ℕ)
    (hoff : (S.alignLeft hleft).offDiag.coeff n = 0)
    (hker : (S.alignLeft hleft).kernel.coeff n = 0) :
    S.active.coeff 0 * S.offDiag.coeff n =
        S.offDiag.coeff 0 * S.active.coeff n ∧
      (S.active.coeff 0)^2 * S.kernel.coeff n =
        (S.offDiag.coeff 0)^2 * S.active.coeff n := by
  have hoff' :
      -(S.offDiag.coeff 0) * S.active.coeff n +
          S.active.coeff 0 * S.offDiag.coeff n = 0 := by
    rw [← S.alignLeft_offDiag_coeff hleft n]
    exact hoff
  have hker' :
      (S.offDiag.coeff 0)^2 * S.active.coeff n -
          2 * S.active.coeff 0 * S.offDiag.coeff 0 * S.offDiag.coeff n +
          (S.active.coeff 0)^2 * S.kernel.coeff n = 0 := by
    rw [← S.alignLeft_kernel_coeff hleft n]
    exact hker
  constructor
  · linear_combination hoff'
  · have hmul := congrArg (fun x => S.offDiag.coeff 0 * x) hoff'
    linear_combination hker' + 2 * hmul

/-- In the right-axis pivot, aligned tangency is literally vanishing of the
raw active and off-diagonal coefficients at that order. -/
theorem rawRayAtOrder_of_alignRight_tangential
    (S : BinarySchurPolynomialSeries R)
    (hright : S.RightAxisPivot)
    (n : ℕ)
    (hoff : (S.alignRight hright).offDiag.coeff n = 0)
    (hker : (S.alignRight hright).kernel.coeff n = 0) :
    S.active.coeff n = 0 ∧ S.offDiag.coeff n = 0 := by
  constructor
  · simpa [alignRight] using hker
  · simpa [alignRight] using hoff

end BinarySchurPolynomialSeries

end

end HC4.Newton
