import HC4.Valuation.CoordinateMaxKernelOpeningLinearPowerPureAxis
import Mathlib.Tactic

/-!
# Literal pure-axis normal form for the degenerate first-opening child

The coefficient-level pure-axis theorem can be repackaged as the exact
polynomial identity

    child = b * X_e^m,

where `e` is the coordinate-max extraction axis and `b != 0`.  This is the
normal form needed by the first-break Hessian calculation.
-/

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

/-- The gradient-ratio linear form is literally supported on the extraction
axis. -/
theorem linearForm_eq_extractionAxis
    (hm : 2 ≤ m) :
    gradientRatioLinearForm P.ratio =
      MvPolynomial.C (P.ratio D.extractionCoordinate) *
        MvPolynomial.X D.extractionCoordinate := by
  classical
  unfold gradientRatioLinearForm
  rw [Finset.sum_eq_single D.extractionCoordinate]
  · rfl
  · intro j _ hje
    rw [P.ratio_eq_zero_of_ne_extraction hm j hje]
    simp
  · simp

/-- Literal nonzero scalar multiplying the pure extraction-axis power. -/
def pureAxisCoefficient : K :=
  P.coefficient * (P.ratio D.extractionCoordinate) ^ m

/-- The pure-axis scalar is nonzero. -/
theorem pureAxisCoefficient_ne_zero
    (hm : 2 ≤ m) :
    P.pureAxisCoefficient D ≠ 0 := by
  unfold pureAxisCoefficient
  exact mul_ne_zero P.coefficient_ne_zero
    (pow_ne_zero _ (P.extraction_ratio_ne_zero hm))

/-- **Exact pure-axis child normal form.** -/
theorem child_eq_pureAxis
    (hm : 2 ≤ m) :
    D.child =
      MvPolynomial.C (P.pureAxisCoefficient D) *
        (MvPolynomial.X D.extractionCoordinate) ^ m := by
  rw [P.eq_power, P.linearForm_eq_extractionAxis hm]
  unfold pureAxisCoefficient
  rw [mul_pow, ← MvPolynomial.C_pow, ← mul_assoc, ← MvPolynomial.C_mul]

end ChildLinearPowerData
end CanonicalCoordinateMaxKernelOpeningData

end

end HC4.Newton
