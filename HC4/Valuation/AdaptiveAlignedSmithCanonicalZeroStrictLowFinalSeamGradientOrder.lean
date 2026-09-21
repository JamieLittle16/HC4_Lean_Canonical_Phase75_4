import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamAxisGradient
import Mathlib.Tactic

/-!
# G6: exact root order of the marked axis-gradient component

G3 gives an exact initial order for one distinguished Hessian entry.  G5
shows that every longitudinal-axis gradient component already vanishes at the
recentered collision endpoint.  Since differentiation in the longitudinal
coordinate is exactly the corresponding Hessian row, the Hessian order can be
integrated once without loss in characteristic zero.

Thus the three strict-low patterns have the following source-honest form:

* pure longitudinal: gradient component 0 has exact order m+1 at x=0;
* low-negative-first: gradient component 2 has exact order m+1 at x=0;
* low-negative-second: gradient component 1 has exact order m+1 at x=0.

Every one of these same gradient components also vanishes at x=-1 by G5.

No progress theorem, repair transition, homogeneity, cocharacter, or JC2 input
is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace HasExactPolynomialInitialOrder

/-- Integrate one exact initial order through a polynomial with zero constant
coefficient.  Characteristic zero is exactly what prevents the derivative
coefficient multiplier from killing a nonzero coefficient. -/
theorem of_derivative_of_coeff_zero
    {P : Polynomial K} {n : ℕ}
    (hzero : P.coeff 0 = 0)
    (hder : HasExactPolynomialInitialOrder P.derivative n) :
    HasExactPolynomialInitialOrder P (n + 1) := by
  constructor
  · intro k hk
    cases k with
    | zero =>
        exact hzero
    | succ r =>
        have hr : r < n := by omega
        have hz := hder.1 r hr
        rw [Polynomial.coeff_derivative] at hz
        have hcast : (((r + 1 : ℕ) : K)) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero r
        exact (mul_eq_zero.mp hz).resolve_right hcast
  · intro hz
    apply hder.2
    rw [Polynomial.coeff_derivative, hz]
    simp

end HasExactPolynomialInitialOrder

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Longitudinal differentiation of an axis-gradient component is precisely
the axis restriction of the Hessian entry with longitudinal first index. -/
theorem finalSeamAxisGradientComponent_derivative
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) :
    (T.finalSeamAxisGradientComponent i).derivative =
      longitudinalAxisRestriction
        (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber
          (0 : Fin 4) i) := by
  change
    (longitudinalAxisRestriction
      (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber)).derivative =
      longitudinalAxisRestriction
        (HC4.Polynomial.hessian T.rightRecenteredSpecialFiber
          (0 : Fin 4) i)
  rw [HC4.Polynomial.hessian_apply]
  rw [← pderiv_comm_commRing]
  exact
    (longitudinalAxisRestriction_pderiv_zero
      (MvPolynomial.pderiv i T.rightRecenteredSpecialFiber)).symm

/-- The exact Hessian order from G3, integrated to the marked gradient
component itself. -/
inductive FinalSeamExactGradientAxisOrder
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | pureLongitudinal
      (m : ℕ)
      (hpattern : IsPureLongitudinalSmithPattern T.terminal.exponent)
      (horder :
        HasExactPolynomialInitialOrder
          (T.finalSeamAxisGradientComponent (0 : Fin 4)) (m + 1))
  | lowNegativeFirst
      (m : ℕ)
      (hpattern : IsLowNegativeFirstSmithPattern T.terminal.exponent)
      (horder :
        HasExactPolynomialInitialOrder
          (T.finalSeamAxisGradientComponent (2 : Fin 4)) (m + 1))
  | lowNegativeSecond
      (m : ℕ)
      (hpattern : IsLowNegativeSecondSmithPattern T.terminal.exponent)
      (horder :
        HasExactPolynomialInitialOrder
          (T.finalSeamAxisGradientComponent (1 : Fin 4)) (m + 1))

/-- Assemble the exact gradient-root order from G3 and G5. -/
theorem finalSeamExactGradientAxisOrder
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.FinalSeamExactGradientAxisOrder := by
  have H := T.finalSeamExactHessianAxisOrder
  cases H with
  | pureLongitudinal m hpure horder =>
      have hder :
          HasExactPolynomialInitialOrder
            (T.finalSeamAxisGradientComponent (0 : Fin 4)).derivative m := by
        rw [T.finalSeamAxisGradientComponent_derivative (0 : Fin 4)]
        exact horder
      have hzero :
          (T.finalSeamAxisGradientComponent (0 : Fin 4)).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        exact T.finalSeamAxisGradientComponent_eval_zero (0 : Fin 4)
      exact .pureLongitudinal m hpure
        (HasExactPolynomialInitialOrder.of_derivative_of_coeff_zero hzero hder)

  | lowNegativeFirst m hfirst horder =>
      have hder :
          HasExactPolynomialInitialOrder
            (T.finalSeamAxisGradientComponent (2 : Fin 4)).derivative m := by
        rw [T.finalSeamAxisGradientComponent_derivative (2 : Fin 4)]
        exact horder
      have hzero :
          (T.finalSeamAxisGradientComponent (2 : Fin 4)).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        exact T.finalSeamAxisGradientComponent_eval_zero (2 : Fin 4)
      exact .lowNegativeFirst m hfirst
        (HasExactPolynomialInitialOrder.of_derivative_of_coeff_zero hzero hder)

  | lowNegativeSecond m hsecond horder =>
      have hder :
          HasExactPolynomialInitialOrder
            (T.finalSeamAxisGradientComponent (1 : Fin 4)).derivative m := by
        rw [T.finalSeamAxisGradientComponent_derivative (1 : Fin 4)]
        exact horder
      have hzero :
          (T.finalSeamAxisGradientComponent (1 : Fin 4)).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        exact T.finalSeamAxisGradientComponent_eval_zero (1 : Fin 4)
      exact .lowNegativeSecond m hsecond
        (HasExactPolynomialInitialOrder.of_derivative_of_coeff_zero hzero hder)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
