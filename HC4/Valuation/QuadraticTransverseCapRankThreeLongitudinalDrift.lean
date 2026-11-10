import HC4.Valuation.QuadraticTransverseCapRankThreeAffineDet
import Mathlib.Tactic

/-!
# Last longitudinal drift contradiction in quadratic transverse rank three

After the transverse collision is combined with the nilpotent
affine-reciprocal normal form, the initial mixed vector vanishes,
hence the entire transverse-linear derivative b'(x) vanishes.

With det C a nonzero CONSTANT and the original unit Hessian
determinant, the axis Schur equation then gives
  det C * a''(x) = 1.
Thus a'' is a nonzero constant. But the original longitudinal
gradient collision requires a'(1)=a'(0), impossible.

This is the complete final scalar contradiction, explicitly
separated from the source ODE and inverse-integrality transport.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Any polynomial 3x3 block admitting a two-sided inverse over
K[x] has a constant nonzero polynomial determinant. This follows
from the concrete determinant of the inverse product, not from
mere generic rank three. -/
omit [CharZero K] in
theorem quadraticTransverse_polynomialMatrixInverse_det_constant
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCM : C * M = 1) :
    ∃ d : K, d ≠ 0 ∧ C.det = Polynomial.C d := by
  have hdet : C.det * M.det = 1 := by
    have h := congrArg Matrix.det hCM
    simpa [Matrix.det_mul] using h
  have hunit : IsUnit C.det := by
    apply isUnit_iff_exists.mpr
    refine ⟨M.det, hdet, ?_⟩
    simpa [mul_comm] using hdet
  obtain ⟨d, _, hconst⟩ := Polynomial.isUnit_iff.mp hunit
  have hd : d ≠ 0 := by
    intro hzero
    have hc : C.det = 0 := by
      simpa [hzero] using hconst.symm
    rw [hc] at hdet
    simp at hdet
  exact ⟨d, hd, hconst.symm⟩

/-- Nonzero constant transverse determinant, zero mixed row, and
the ACTUAL marked longitudinal collision force contradiction.
The constant-Hessian determinant equation here is concrete
and leaves no abstract rank-three closing hypothesis. -/
theorem quadraticTransverse_rankThree_constantDet_longitudinalCollision_impossible
    (a : Polynomial K)
    (d : K)
    (hd : d ≠ 0)
    (haxis :
      Polynomial.C d *
        Polynomial.derivative (Polynomial.derivative a) = 1)
    (hcoll :
      Polynomial.eval (1 : K) (Polynomial.derivative a) =
        Polynomial.eval (0 : K) (Polynomial.derivative a)) :
    False := by
  have hsecond :
      Polynomial.derivative (Polynomial.derivative a) =
        Polynomial.C (d⁻¹) := by
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr hd)
    calc
      Polynomial.C d *
          Polynomial.derivative (Polynomial.derivative a) = 1 := haxis
      _ = Polynomial.C d * Polynomial.C (d⁻¹) := by
        rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  exact polynomial_nonzeroConstantDerivative_no_unitIntervalCollision
    (Polynomial.derivative a) (d⁻¹)
    (inv_ne_zero hd) hsecond hcoll

end

end HC4.Valuation
