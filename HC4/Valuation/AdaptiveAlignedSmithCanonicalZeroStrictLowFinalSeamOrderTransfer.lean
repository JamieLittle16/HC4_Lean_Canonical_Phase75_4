import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamGradientOrder
import Mathlib.Tactic

/-!
# G7: determinant-one transfer of collision-root order

Every longitudinal-axis gradient component vanishes at the recentered
collision origin.  G6 singles out one marked component and gives its exact
root multiplicity.

If that marked multiplicity is greater than one, its longitudinal derivative
-- the corresponding row-zero Hessian entry -- vanishes at the origin.
Because the full origin Hessian has determinant one, row zero cannot vanish.
Hence a *different* gradient component has nonzero longitudinal derivative at
the origin.  Since its value is already zero there, that other component has
exact root order one.

This is the first determinant-one coupling between the marked strict-low fibre
and the remaining gradient components.  It is an order-transfer statement,
not a contradiction and not a progress edge.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A nonzero row-zero origin Hessian entry is exactly a simple root of the
corresponding longitudinal-axis gradient component. -/
theorem finalSeamAxisGradientComponent_exactOrder_one_of_originEntry_ne_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (j : Fin 4)
    (hne : T.finalSeamOriginHessian (0 : Fin 4) j ≠ 0) :
    HasExactPolynomialInitialOrder
      (T.finalSeamAxisGradientComponent j) 1 := by
  have hzero :
      (T.finalSeamAxisGradientComponent j).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact T.finalSeamAxisGradientComponent_eval_zero j
  have hone :
      (T.finalSeamAxisGradientComponent j).coeff 1 ≠ 0 := by
    intro hz
    apply hne
    rw [T.finalSeamOriginHessian_eq_coeff_zero]
    rw [← T.finalSeamAxisGradientComponent_derivative j]
    rw [Polynomial.coeff_derivative, hz]
    simp
  constructor
  · intro k hk
    have hk0 : k = 0 := by omega
    simpa [hk0] using hzero
  · exact hone

/-- If a marked axis-gradient component has exact order `m+1` with
`m > 0`, its corresponding origin Hessian entry vanishes. -/
theorem finalSeamOriginHessian_marked_eq_zero_of_gradientOrder_succ_pos
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) (m : ℕ)
    (horder :
      HasExactPolynomialInitialOrder
        (T.finalSeamAxisGradientComponent i) (m + 1))
    (hm : 0 < m) :
    T.finalSeamOriginHessian (0 : Fin 4) i = 0 := by
  have hcoeff1 :
      (T.finalSeamAxisGradientComponent i).coeff 1 = 0 :=
    horder.1 1 (by omega)
  rw [T.finalSeamOriginHessian_eq_coeff_zero]
  rw [← T.finalSeamAxisGradientComponent_derivative i]
  rw [Polynomial.coeff_derivative, hcoeff1]
  simp

/-- **Exact order transfer.**

A higher-order marked collision root forces a distinct simple collision root
in another gradient component. -/
theorem finalSeam_exists_other_exactOrder_one_of_markedOrder_succ_pos
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (i : Fin 4) (m : ℕ)
    (horder :
      HasExactPolynomialInitialOrder
        (T.finalSeamAxisGradientComponent i) (m + 1))
    (hm : 0 < m) :
    ∃ j : Fin 4,
      j ≠ i ∧
      HasExactPolynomialInitialOrder
        (T.finalSeamAxisGradientComponent j) 1 := by
  let H := T.finalSeamOriginHessian
  have hdet : H.det ≠ 0 := by
    rw [T.finalSeamOriginHessian_det_one]
    exact one_ne_zero
  have hi0 : H (0 : Fin 4) i = 0 := by
    exact
      T.finalSeamOriginHessian_marked_eq_zero_of_gradientOrder_succ_pos
        i m horder hm
  rcases matrix4_det_ne_zero_row_exists_entry H hdet (0 : Fin 4) with
    ⟨j, hj⟩
  have hji : j ≠ i := by
    intro h
    subst j
    exact hj hi0
  exact ⟨j, hji,
    T.finalSeamAxisGradientComponent_exactOrder_one_of_originEntry_ne_zero
      j hj⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
