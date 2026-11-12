import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3NonlinearGradedSourceFrontier
import Mathlib.Tactic

/-!
# E3 diagnostic: positive transverse grades are invisible on the marked axis

The marked collision compares the gradient at two points on the longitudinal
coordinate-0 axis.  A first actual transverse face of degree r >= 3
is homogeneous of positive transverse weight and has no constant,
linear, or quadratic transverse jet on that axis.

This is a rigorous obstruction to an otherwise tempting inference:
the nonzero positive-weight Hessian minor extracted in the nonlinear
E3 rank-two branch cannot be evaluated at either marked point to yield
a nonzero scalar.  Both its positive-weight component and every
Hessian entry of the first actual face vanish on the entire axis.

Consequently a new contradiction must use the determinant-one
identity *off* the axis, together with lower transverse-degree terms,
not merely the two marked endpoint values.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Every strictly positive transverse-weight component restricts
identically to zero on the longitudinal axis.  This applies to any
four-variable source polynomial without determinant or collision
hypotheses. -/
theorem transversePositiveInitialForm_axisRestriction_zero
    (F : MvPolynomial (Fin 4) K)
    (m : ℤ) (hm : 0 < m) :
    longitudinalAxisRestriction
      (HC4.Polynomial.initialForm
        (fun i => (topKernelMarkedAxisNatWeight i : ℤ)) m F) = 0 := by
  rw [longitudinalAxisRestriction_eq_coefficient_zero]
  apply Polynomial.ext
  intro a
  rw [coeff_longitudinalCoefficientPolynomialAt_eq_sourceCoeff,
    HC4.Polynomial.coeff_initialForm]
  have hw :
      Finsupp.weight
          (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
          ((0 : Fin 3 →₀ ℕ).cons a) = 0 := by
    rw [weight_topKernelMarkedAxisIntWeight]
    simp
  have hzero : (0 : ℤ) ≠ m := ne_of_lt hm
  simp [hw, hzero]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The first actual nonlinear E3 face has zero Hessian everywhere on
the longitudinal axis, not merely at the two marked collision points.
Its transverse degree at least three makes every Hessian entry carry
positive transverse weight. -/
theorem PureLongitudinalMarkedE3Data.firstActualHessian_axisRestriction_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (i j : Fin 4) :
    longitudinalAxisRestriction
      (HC4.Polynomial.hessian
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j) = 0 := by
  rw [P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
      D.coefficient_ne_zero D.topFace_eq]
  rw [HC4.Polynomial.hessian_initialForm_entry]
  have hr : 3 ≤
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder :=
    D.firstActualTransverseDegree_ge_three P
  have hi : (topKernelMarkedAxisNatWeight i : ℤ) ≤ 1 := by
    fin_cases i <;> norm_num [topKernelMarkedAxisNatWeight]
  have hj : (topKernelMarkedAxisNatWeight j : ℤ) ≤ 1 := by
    fin_cases j <;> norm_num [topKernelMarkedAxisNatWeight]
  apply transversePositiveInitialForm_axisRestriction_zero
  omega

/-- In the graded source-minor branch the exact positive-weight component
of the represented-source Hessian minor is zero on the longitudinal
axis, despite being globally nonzero.  Thus endpoint evaluation of
that component alone gives no collision obstruction. -/
theorem PureLongitudinalMarkedE3Data.sourceGradedMinor_axisRestriction_zero
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (i j k l : Fin 4) :
    let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
    let w : Fin 4 → ℤ := fun a => (topKernelMarkedAxisNatWeight a : ℤ)
    let e : ℤ := ((r : ℤ) - w i - w k) + ((r : ℤ) - w j - w l)
    longitudinalAxisRestriction
      (HC4.Polynomial.initialForm w e
        (hessianTwoByTwoMinor T.topKernelReesSource i j k l)) = 0 := by
  let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  let w : Fin 4 → ℤ := fun a => (topKernelMarkedAxisNatWeight a : ℤ)
  let e : ℤ := ((r : ℤ) - w i - w k) + ((r : ℤ) - w j - w l)
  have hr : 3 ≤ r := D.firstActualTransverseDegree_ge_three P
  have hi : w i ≤ 1 := by
    dsimp [w]
    fin_cases i <;> norm_num [topKernelMarkedAxisNatWeight]
  have hj : w j ≤ 1 := by
    dsimp [w]
    fin_cases j <;> norm_num [topKernelMarkedAxisNatWeight]
  have hk : w k ≤ 1 := by
    dsimp [w]
    fin_cases k <;> norm_num [topKernelMarkedAxisNatWeight]
  have hl : w l ≤ 1 := by
    dsimp [w]
    fin_cases l <;> norm_num [topKernelMarkedAxisNatWeight]
  have he : 0 < e := by
    dsimp [e]
    omega
  change longitudinalAxisRestriction
      (HC4.Polynomial.initialForm
        (fun a => (topKernelMarkedAxisNatWeight a : ℤ)) e
        (hessianTwoByTwoMinor T.topKernelReesSource i j k l)) = 0
  exact transversePositiveInitialForm_axisRestriction_zero
    (hessianTwoByTwoMinor T.topKernelReesSource i j k l) e he

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
end
end HC4.Valuation
