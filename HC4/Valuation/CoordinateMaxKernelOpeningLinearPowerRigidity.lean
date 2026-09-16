import HC4.Valuation.CoordinateMaxKernelOpeningDegenerateClassification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreDirectionLock
import Mathlib.Tactic

/-!
# Linear-power rigidity at an honest coordinate-max kernel opening

The degenerate child frontier leaves an exact homogeneous child

    child = a * L^m

with `m >= 2`.  At a canonical first kernel opening the child has a literal
coordinate kernel.  Since the child is nonzero in characteristic zero, the
coefficient of that kernel coordinate in `L` must vanish.

This is deliberately only a source-level rigidity statement.  It introduces
no repair step and no clock comparison.
-/

namespace HC4.Newton

noncomputable section

open HC4.Polynomial
open HC4.Valuation

variable {K : Type*} [Field K] [CharZero K]

namespace CanonicalCoordinateMaxKernelOpeningData

variable {F : MvPolynomial (Fin 4) K}
variable (D : CanonicalCoordinateMaxKernelOpeningData F)

namespace ChildLinearPowerData

variable {m : ℕ}
variable (P : D.ChildLinearPowerData m)

/-- The scalar in a nonzero linear-power child is nonzero. -/
theorem coefficient_ne_zero : P.coefficient ≠ 0 := by
  intro ha
  apply D.child_ne_zero
  rw [P.eq_power, ha]
  simp

/-- For positive degree the linear form in a nonzero linear-power child is
itself nonzero. -/
theorem linearForm_ne_zero
    (hm : 0 < m) :
    gradientRatioLinearForm P.ratio ≠ 0 := by
  intro hL
  apply D.child_ne_zero
  rw [P.eq_power, hL]
  simp [hm]

/-- The first-opening kernel direction is absent from the exact linear form. -/
theorem kernel_ratio_eq_zero
    (hm : 2 ≤ m) :
    P.ratio D.kernelCoordinate = 0 := by
  have hmpos : 0 < m := by omega
  have ha : P.coefficient ≠ 0 := P.coefficient_ne_zero
  have hL : gradientRatioLinearForm P.ratio ≠ 0 := P.linearForm_ne_zero hmpos
  have hpow :
      (gradientRatioLinearForm P.ratio) ^ (m - 1) ≠ 0 :=
    pow_ne_zero _ hL
  have hmK : (m : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hmpos)

  have hderiv :
      MvPolynomial.C P.coefficient *
          MvPolynomial.C ((m : K) * P.ratio D.kernelCoordinate) *
          (gradientRatioLinearForm P.ratio) ^ (m - 1) = 0 := by
    calc
      MvPolynomial.C P.coefficient *
            MvPolynomial.C ((m : K) * P.ratio D.kernelCoordinate) *
            (gradientRatioLinearForm P.ratio) ^ (m - 1) =
          MvPolynomial.pderiv D.kernelCoordinate
            (MvPolynomial.C P.coefficient *
              (gradientRatioLinearForm P.ratio) ^ m) := by
                rw [MvPolynomial.pderiv_C_mul]
                have hmrepr : m = (m - 1) + 1 := by omega
                conv_rhs =>
                  rhs
                  rw [hmrepr]
                rw [pderiv_gradientRatioLinearForm_pow_succ]
                congr 2
                push_cast
                ring
      _ = MvPolynomial.pderiv D.kernelCoordinate D.child := by
            rw [P.eq_power]
      _ = 0 := D.child_kernel

  by_contra hc
  have hCa : MvPolynomial.C P.coefficient ≠ 0 := by simpa using ha
  have hscalar : (m : K) * P.ratio D.kernelCoordinate ≠ 0 :=
    mul_ne_zero hmK hc
  have hCs :
      MvPolynomial.C ((m : K) * P.ratio D.kernelCoordinate) ≠ 0 := by
    simpa using hscalar
  exact (mul_ne_zero (mul_ne_zero hCa hCs) hpow) hderiv

end ChildLinearPowerData

end CanonicalCoordinateMaxKernelOpeningData

end

end HC4.Newton
