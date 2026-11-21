import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelFirstBreakKernelLinear
import Mathlib.Tactic

/-!
# Affine-in-kernel normal form of the final top-kernel residual

The kernel-linear support packet can be integrated exactly in the stored
kernel coordinate.  For the exact lower layer G set

    A = pderiv k G
    B = G - X_k * A.

Because the pure kernel Hessian entry vanishes, A is independent of k.
Differentiating B then gives zero as well, so

    G = X_k * A + B

with both A and B independent of k.  The retained nonzero mixed Hessian entry
is exactly a nonzero transverse derivative of A.

This is the explicit affine normal form needed for determinant-coefficient and
staircase calculations.  No terminal cocharacter, progress theorem, or JC2
input is used.
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

/-- Exact affine decomposition of the surviving lower layer in the stored
kernel coordinate. -/
structure ExactKernelAffineOrdinaryLayerData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  source : P.ExactKernelLinearCoupledOrdinaryLayerData
  A : MvPolynomial (Fin 4) K
  B : MvPolynomial (Fin 4) K
  A_eq :
    A =
      MvPolynomial.pderiv kernelCoordinate
        source.residual.exactNonlinearMixedLayer
  B_eq :
    B =
      source.residual.exactNonlinearMixedLayer -
        MvPolynomial.X kernelCoordinate * A
  decomposition :
    source.residual.exactNonlinearMixedLayer =
      MvPolynomial.X kernelCoordinate * A + B
  A_kernel_free :
    MvPolynomial.pderiv kernelCoordinate A = 0
  B_kernel_free :
    MvPolynomial.pderiv kernelCoordinate B = 0
  mixedDerivative_ne_zero :
    MvPolynomial.pderiv source.residual.mixed.layer.index A ≠ 0

/-- The kernel-linear mixed residual has a literal affine-in-kernel
decomposition. -/
theorem ExactKernelLinearCoupledOrdinaryLayerData.toAffineData
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.ExactKernelLinearCoupledOrdinaryLayerData) :
    Nonempty P.ExactKernelAffineOrdinaryLayerData := by
  let G := S.residual.exactNonlinearMixedLayer
  let i := S.residual.mixed.layer.index
  let A := MvPolynomial.pderiv kernelCoordinate G
  let B := G - MvPolynomial.X kernelCoordinate * A

  have hAk : MvPolynomial.pderiv kernelCoordinate A = 0 := by
    dsimp [A, G]
    simpa [exactNonlinearMixedLayer, HC4.Polynomial.hessian_apply] using
      S.residual.mixed.kernelDiagonal_eq_zero

  have hBk : MvPolynomial.pderiv kernelCoordinate B = 0 := by
    dsimp [B]
    rw [map_sub, MvPolynomial.pderiv_mul]
    dsimp [A]
    rw [hAk]
    simp

  have hmix :
      MvPolynomial.pderiv i A ≠ 0 := by
    have hH :
        HC4.Polynomial.hessian G i kernelCoordinate ≠ 0 := by
      simpa [G, i, exactNonlinearMixedLayer] using
        S.residual.mixed.mixed_ne_zero
    intro hzero
    apply hH
    change
      MvPolynomial.pderiv kernelCoordinate
          (MvPolynomial.pderiv i G) = 0
    rw [← pderiv_comm_backport i kernelCoordinate G]
    simpa [A] using hzero

  refine ⟨{
    source := S
    A := A
    B := B
    A_eq := rfl
    B_eq := rfl
    decomposition := ?_
    A_kernel_free := hAk
    B_kernel_free := hBk
    mixedDerivative_ne_zero := hmix
  }⟩
  dsimp [B]
  ring

/-- Final top-kernel frontier in explicit affine normal form. -/
theorem actualRankTwo_or_exactKernelAffineLayer
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactKernelAffineOrdinaryLayerData := by
  rcases P.actualRankTwo_or_exactKernelLinearCoupledLayer with
    hactual | hlinear
  · exact Or.inl hactual
  · rcases hlinear with ⟨S⟩
    exact Or.inr S.toAffineData

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
