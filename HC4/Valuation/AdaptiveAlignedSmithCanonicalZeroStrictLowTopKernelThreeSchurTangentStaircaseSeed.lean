import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurTangentLinearPower
import Mathlib.Tactic

/-!
# Explicit staircase seed in the tangent three-Schur branch

The previous stage proves that for the first lower ordinary source layer G_E,

    partial_k G_E = beta * L_tilde^(E-1),

where k is the stored top-face kernel coordinate and L_tilde is the top
linear direction normalized at the scalar Schur pivot.

Since the same first-break packet has

    partial_k^2 G_E = 0,

the layer integrates exactly as

    G_E = beta * X_k * L_tilde^(E-1) + B_E,

with partial_k B_E = 0.  The coefficient beta is nonzero because the retained
mixed Hessian entry forces the pivot derivative of partial_k G_E to be
nonzero.

This is the literal first arithmetic-staircase layer on the honest source
reverse-Rees family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Explicit source-layer normal form left by the tangent first break. -/
structure ThreeSchurTangentStaircaseSeedData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1) where
  tangent : ThreeSchurTangentAtFirstBreak S M
  coefficient : K
  coefficient_ne_zero : coefficient ≠ 0
  kernelFreePart : MvPolynomial (Fin 4) K
  layer_eq :
    M.sourceLayer =
      MvPolynomial.C coefficient *
          MvPolynomial.X kernelCoordinate *
          (gradientRatioLinearForm S.normalizedTopRatio) ^
            (M.mixed.layer.sourceDegree - 1) +
        kernelFreePart
  kernelFree :
    MvPolynomial.pderiv kernelCoordinate kernelFreePart = 0

/-- **Tangent staircase seed.**

The first lower tangent layer is exactly one nonzero kernel-linear power in
the top direction plus a kernel-free remainder. -/
theorem ThreeSchurTangentAtFirstBreak.toStaircaseSeedData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    Nonempty (ThreeSchurTangentStaircaseSeedData S M) := by
  rcases R.toKernelDerivativeLinearPowerData with ⟨L⟩
  let A : MvPolynomial (Fin 4) K :=
    MvPolynomial.pderiv kernelCoordinate M.sourceLayer
  let B : MvPolynomial (Fin 4) K :=
    M.sourceLayer - MvPolynomial.X kernelCoordinate * A

  have hAeq :
      A =
        MvPolynomial.C L.coefficient *
          (gradientRatioLinearForm S.normalizedTopRatio) ^
            (M.mixed.layer.sourceDegree - 1) := by
    simpa [A] using L.kernelDerivative_eq_power

  have hcoef : L.coefficient ≠ 0 := by
    intro hz
    have hA0 : A = 0 := by
      rw [hAeq, hz]
      simp
    apply R.kernelDerivative_pivot_ne_zero
    rw [show
      MvPolynomial.pderiv kernelCoordinate M.sourceLayer = A by rfl,
      hA0]
    simp

  have hAk : MvPolynomial.pderiv kernelCoordinate A = 0 := by
    dsimp [A]
    simpa [ExactNonlinearMixedOrdinaryLayerAtFirstBreak.sourceLayer,
      HC4.Polynomial.hessian_apply] using
      M.mixed.kernelDiagonal_eq_zero

  have hBk : MvPolynomial.pderiv kernelCoordinate B = 0 := by
    dsimp [B]
    rw [map_sub, MvPolynomial.pderiv_mul]
    rw [show
      MvPolynomial.pderiv kernelCoordinate
          (MvPolynomial.X kernelCoordinate) = 1 by simp]
    rw [hAk]
    rw [show
      MvPolynomial.pderiv kernelCoordinate M.sourceLayer = A by rfl]
    simp

  have hdecomp :
      M.sourceLayer =
        MvPolynomial.C L.coefficient *
            MvPolynomial.X kernelCoordinate *
            (gradientRatioLinearForm S.normalizedTopRatio) ^
              (M.mixed.layer.sourceDegree - 1) +
          B := by
    calc
      M.sourceLayer =
          MvPolynomial.X kernelCoordinate * A + B := by
            dsimp [B]
            ring
      _ =
          MvPolynomial.C L.coefficient *
              MvPolynomial.X kernelCoordinate *
              (gradientRatioLinearForm S.normalizedTopRatio) ^
                (M.mixed.layer.sourceDegree - 1) +
            B := by
              rw [hAeq]
              ring

  exact ⟨{
    tangent := R
    coefficient := L.coefficient
    coefficient_ne_zero := hcoef
    kernelFreePart := B
    layer_eq := hdecomp
    kernelFree := hBk
  }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
