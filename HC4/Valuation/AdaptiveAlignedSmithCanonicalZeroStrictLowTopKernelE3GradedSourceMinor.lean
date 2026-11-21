import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3NonlinearSourceRankTwoFrontier
import Mathlib.Tactic

/-!
# The exact positive transverse-weight component of nonlinear E3 source minors

An arbitrary nonzero two-by-two Hessian minor of the first actual marked-axis
face is stronger than a generic rank-two witness on the represented source.
The maximal-weight Hessian-minor identity identifies it *exactly* with a
specific transverse-weight component of the represented-source minor.

For first-actual transverse degree r >= 3, the component has weight

  (r - w_i - w_k) + (r - w_j - w_l) >= 2,

where w_0 = 0 and w_1 = w_2 = w_3 = 1.

This retains a genuinely positive graded datum that the previous
source-rank-two frontier forgot.  A nonzero generic source minor, by itself,
does not imply that this particular component is nonzero.
-/

namespace HC4.Valuation
noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The exact maximal transverse-weight component of the *original
represented-source* two-by-two Hessian minor equals the corresponding
minor of the actual first layer.  This does not invoke any layerwise
cancellation assumption. -/
theorem PureLongitudinalMarkedE3Data.firstActualTwoByTwoMinor_sourceGradedIdentity
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (i j k l : Fin 4) :
    let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
    let w : Fin 4 → ℤ := fun a => (topKernelMarkedAxisNatWeight a : ℤ)
    HC4.Polynomial.initialForm w
        (((r : ℤ) - w i - w k) + ((r : ℤ) - w j - w l))
        (hessianTwoByTwoMinor T.topKernelReesSource i j k l) =
      hessianTwoByTwoMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j k l := by
  let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
  let w : Fin 4 → ℤ := fun a => (topKernelMarkedAxisNatWeight a : ℤ)
  have hbound : HC4.Polynomial.IsWeightLE
      w (r : ℤ) T.topKernelReesSource := by
    intro d hd
    have hnat :=
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        D.coefficient_ne_zero D.topFace_eq d hd
    rw [weight_topKernelMarkedAxisIntWeight]
    rw [weight_topKernelMarkedAxisNatWeight] at hnat
    exact_mod_cast hnat
  change
    HC4.Polynomial.initialForm w
        (((r : ℤ) - w i - w k) + ((r : ℤ) - w j - w l))
        (hessianTwoByTwoMinor T.topKernelReesSource i j k l) =
      hessianTwoByTwoMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j k l
  rw [P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
    D.coefficient_ne_zero D.topFace_eq]
  exact e3InitialForm_hessianTwoByTwoMinor_eq hbound i j k l

/-- Whenever the first actual face carries a nonzero two-by-two Hessian
minor, the original represented-source minor has a nonzero component
at a *strictly positive* transverse weight (in fact at least two). -/
theorem PureLongitudinalMarkedE3Data.firstActualTwoByTwoMinor_sourcePositiveGraded
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (i j k l : Fin 4)
    (hminor :
      hessianTwoByTwoMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j k l ≠ 0) :
    let r := T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder
    let w : Fin 4 → ℤ := fun a => (topKernelMarkedAxisNatWeight a : ℤ)
    let e : ℤ := ((r : ℤ) - w i - w k) + ((r : ℤ) - w j - w l)
    2 ≤ e ∧
      HC4.Polynomial.initialForm w e
        (hessianTwoByTwoMinor T.topKernelReesSource i j k l) ≠ 0 := by
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
  have he : 2 ≤ e := by
    dsimp [e]
    omega
  have hgraded :=
    D.firstActualTwoByTwoMinor_sourceGradedIdentity P i j k l
  change
    HC4.Polynomial.initialForm w e
        (hessianTwoByTwoMinor T.topKernelReesSource i j k l) =
      hessianTwoByTwoMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j k l at hgraded
  change 2 ≤ e ∧
    HC4.Polynomial.initialForm w e
      (hessianTwoByTwoMinor T.topKernelReesSource i j k l) ≠ 0
  exact ⟨he, hgraded.symm ▸ hminor⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
