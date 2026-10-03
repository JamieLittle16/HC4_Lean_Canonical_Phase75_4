import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# Leading longitudinal determinant coefficient above a rank-two initial block

The coefficient of the highest longitudinal power in the model Hessian has
zero `(0,0)` entry. Its first two rows start at parameter order two and its
constant transverse block is nondegenerate. The coefficient at order four
therefore detects the square of the `(0,1)` departure. All polynomial tails
below are arbitrary; no later-layer coefficients are discarded.

This is a finite four-block identity. Identifying this block with the leading
longitudinal coefficient of an arbitrary terminal remains a separate task.
-/

namespace HC4.Newton
noncomputable section

variable {R : Type*} [CommRing R]

/-- A longitudinal leading block with rank-two constant transverse part. -/
def longitudinalRankTwoInitialBlock
    (B P Q D E F U V W : Polynomial R) : GeneralFourBlock (Polynomial R) where
  a := 0
  b := Polynomial.X^2 * B
  p := Polynomial.X^2 * P
  q := Polynomial.X^2 * Q
  d := Polynomial.X^2 * D
  r := Polynomial.X^2 * E
  s := Polynomial.X^2 * F
  x := U
  y := V
  z := W

/-- The first possible determinant coefficient is an exact negative square
times the retained transverse determinant, with arbitrary polynomial tails. -/
theorem longitudinalRankTwoInitialBlock_coeff_four
    (B P Q D E F U V W : Polynomial R) :
    (longitudinalRankTwoInitialBlock B P Q D E F U V W).determinantCore.coeff 4 =
      -(B.coeff 0)^2 * (U.coeff 0 * W.coeff 0 - (V.coeff 0)^2) := by
  have hfactor :
      (longitudinalRankTwoInitialBlock B P Q D E F U V W).determinantCore =
        Polynomial.X^4 *
          (-B^2 * (U*W - V^2) + Polynomial.X^2 *
            (2*B*P*E*W - 2*B*P*F*V - 2*B*Q*E*V + 2*B*Q*F*U -
              D*P^2*W + 2*D*P*Q*V - D*Q^2*U) +
            Polynomial.X^4 * (P^2*F^2 - 2*P*Q*E*F + Q^2*E^2)) := by
    simp only [longitudinalRankTwoInitialBlock, GeneralFourBlock.determinantCore]
    ring
  rw [hfactor, Polynomial.coeff_X_pow_mul' ]
  simp [Polynomial.coeff_zero_eq_eval_zero]

/-- A nonzero retained transverse minor eliminates the omitted departure. -/
theorem longitudinalRankTwoInitialBlock_first_entry_eq_zero
    [IsDomain R] (B P Q D E F U V W : Polynomial R)
    (hminor : U.coeff 0 * W.coeff 0 - (V.coeff 0)^2 ≠ 0)
    (hzero :
      (longitudinalRankTwoInitialBlock B P Q D E F U V W).determinantCore.coeff 4 = 0) :
    B.coeff 0 = 0 := by
  rw [longitudinalRankTwoInitialBlock_coeff_four] at hzero
  have hneg := (mul_eq_zero.mp hzero).resolve_right hminor
  exact pow_eq_zero (neg_eq_zero.mp hneg)

/-- Exact specialization of the coefficient that detects the previously
omitted `k*y*u^2` term in the level-nine model. -/
theorem ray_kernel_omitted_term_top_coefficient
    (k z w : R) (B P Q D E F U V W : Polynomial R) :
    (longitudinalRankTwoInitialBlock
      (Polynomial.C (18*k) + Polynomial.X*B) P Q D E F
      (Polynomial.C (6*w^3*z) + Polynomial.X*U)
      (Polynomial.C (9*w^2*z^2) + Polynomial.X*V)
      (Polynomial.C (6*w*z^3) + Polynomial.X*W)).determinantCore.coeff 4 =
        14580*k^2*w^4*z^4 := by
  rw [longitudinalRankTwoInitialBlock_coeff_four]
  simp [Polynomial.coeff_zero_eq_eval_zero]
  ring

end
end HC4.Newton
