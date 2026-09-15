import HC4.Valuation.CoordinateMaxKernelOpeningPureAxisNormalForm
import Mathlib.Tactic

/-!
# Nonzero Hessian anchor on the pure extraction axis

For a nonzero homogeneous linear power `a * L^m`, the diagonal Hessian entry
in any direction where `L` has nonzero coefficient is nonzero once `m >= 2`.
Applied to the extraction coefficient forced nonzero by the coordinate-max
first-opening provenance, this gives the constant special-fibre Hessian anchor
needed by the rank-one first-break theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Four-variable/general-finite-variable version of the standard Hessian
formula for a scalar power of the gradient-ratio linear form. -/
theorem hessian_C_mul_gradientRatioLinearForm_pow_add_two_fin
    {nvar : ℕ}
    (a : K)
    (c : Fin nvar → K)
    (n : ℕ)
    (i j : Fin nvar) :
    HC4.Polynomial.hessian
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (n + 2)) i j =
      MvPolynomial.C
          (a * (((n + 2 : ℕ) : K)) * (((n + 1 : ℕ) : K)) * c i * c j) *
        (gradientRatioLinearForm c) ^ n := by
  simp only [HC4.Polynomial.hessian_apply]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_gradientRatioLinearForm_pow_succ c i (n + 1)]
  rw [MvPolynomial.pderiv_C_mul]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_gradientRatioLinearForm_pow_succ c j n]
  push_cast
  simp only [MvPolynomial.C_mul]
  ring

end
end HC4.Valuation

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData
namespace ChildLinearPowerData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)
variable {m : ℕ}
variable (P : D.ChildLinearPowerData m)

/-- The pure extraction axis contributes a literal nonzero Hessian diagonal
entry on the special-fibre child. -/
theorem extraction_hessian_ne_zero
    (hm : 3 ≤ m) :
    HC4.Polynomial.hessian D.child
      D.extractionCoordinate D.extractionCoordinate ≠ 0 := by
  have hrepr : m = (m - 2) + 2 := by omega
  have ha : P.coefficient ≠ 0 := P.coefficient_ne_zero
  have hc : P.ratio D.extractionCoordinate ≠ 0 :=
    P.extraction_ratio_ne_zero (by omega)
  have hL : gradientRatioLinearForm P.ratio ≠ 0 :=
    P.linearForm_ne_zero (by omega)
  have hn2 : (((m - 2 + 2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (show m - 2 + 2 ≠ 0 by omega)
  have hn1 : (((m - 2 + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (show m - 2 + 1 ≠ 0 by omega)
  rw [P.eq_power, hrepr]
  rw [hessian_C_mul_gradientRatioLinearForm_pow_add_two_fin]
  apply mul_ne_zero
  · simp only [MvPolynomial.C_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hn2) hn1) hc) hc
  · exact pow_ne_zero _ hL

end ChildLinearPowerData
end CanonicalCoordinateMaxKernelOpeningData

end

end HC4.Newton
