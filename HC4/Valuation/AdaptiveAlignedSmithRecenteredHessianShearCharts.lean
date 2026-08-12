import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianSpecialFiber
import Mathlib.Tactic

/-!
# Determinant-preserving shear charts for the recentered adaptive Hessian

The coordinate-principal chart trichotomy leaves one honest residual case:
every displayed coordinate-principal `2 x 2` active minor may vanish.  It is
not valid, over a general symmetric matrix, to identify that condition alone
with rank at most one.

The correct next move is a unimodular change of active plane.  At the level of
a general symmetric four-block we use the elementary shear

    e₀  ↦  e₀ + e₂,

leaving the other three basis vectors fixed.  The transformed block is still
symmetric and its full determinant is unchanged.  More importantly its active
minor is

    Δ'₀₁ = Δ₀₁
           + 2 (H₀₂ H₁₁ - H₀₁ H₁₂)
           + Δ₂₁.

Thus, once the two coordinate-principal minors `Δ₀₁` and `Δ₂₁` vanish, any
nonzero three-index cross minor immediately creates a nonzero active chart.
The already-green exact Schur / zero-Schur machinery then applies with no new
termination argument.

Iterating this identity after coordinate permutations is the algebraic route
from the old `allActiveMinorsZero` branch to the genuine determinantal
rank-one relations.  No JC2 input occurs in this file.
-/

namespace HC4.Newton

noncomputable section

universe v

variable {R : Type v} [CommRing R]

namespace GeneralFourBlock

/-- Elementary determinant-one shear of the displayed symmetric four-block,
corresponding to replacing the first basis vector by `e₀ + e₂`. -/
noncomputable def shear02 (H : GeneralFourBlock R) : GeneralFourBlock R where
  a := H.a + 2 * H.p + H.x
  b := H.b + H.r
  d := H.d
  p := H.p + H.x
  q := H.q + H.y
  r := H.r
  s := H.s
  x := H.x
  y := H.y
  z := H.z

/-- The elementary `e₀ ↦ e₀ + e₂` shear preserves the complete four-block
determinant identically over every commutative ring. -/
theorem shear02_determinantCore (H : GeneralFourBlock R) :
    H.shear02.determinantCore = H.determinantCore := by
  unfold shear02 determinantCore
  ring

/-- Exact active-minor formula under the elementary shear. -/
theorem shear02_activeDet (H : GeneralFourBlock R) :
    H.shear02.activeDet =
      H.activeDet +
        2 * (H.p * H.d - H.b * H.r) +
        (H.x * H.d - H.r * H.r) := by
  unfold shear02 activeDet
  ring

/-- If the two old principal minors vanish, the sheared active determinant is
exactly twice the intervening three-index cross minor. -/
theorem shear02_activeDet_of_principal_zero
    (H : GeneralFourBlock R)
    (h01 : H.activeDet = 0)
    (h21 : H.x * H.d - H.r * H.r = 0) :
    H.shear02.activeDet =
      2 * (H.p * H.d - H.b * H.r) := by
  rw [H.shear02_activeDet, h01, h21]
  ring

end GeneralFourBlock

end

end HC4.Newton

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-! ## Constant coefficient and the shear -/

/-- Parameter-zero specialisation commutes with the elementary block shear. -/
theorem parameterConstantCoeffFourBlock_shear02
    (H : GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K))) :
    parameterConstantCoeffFourBlock H.shear02 =
      (parameterConstantCoeffFourBlock H).shear02 := by
  ext <;>
    simp [parameterConstantCoeffFourBlock,
      GeneralFourBlock.shear02,
      Polynomial.coeff_zero_eq_eval_zero]

/-- Constant coefficient of the sheared active determinant, written entirely
in terms of the constant coefficients of the unsheared block. -/
theorem shear02_activeDet_coeff_zero
    (H : GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K))) :
    H.shear02.activeDet.coeff 0 =
      H.activeDet.coeff 0 +
        2 *
          (H.p.coeff 0 * H.d.coeff 0 -
            H.b.coeff 0 * H.r.coeff 0) +
        (H.x.coeff 0 * H.d.coeff 0 -
          H.r.coeff 0 * H.r.coeff 0) := by
  rw [GeneralFourBlock.shear02_activeDet]
  simp [Polynomial.coeff_zero_eq_eval_zero]

/-- After the two coordinate-principal constant minors vanish, a nonzero
three-index cross minor makes the sheared active minor nonzero. -/
theorem shear02_activeDet_coeff_zero_ne_zero_of_cross
    [CharZero K]
    (H : GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K)))
    (h01 : H.activeDet.coeff 0 = 0)
    (h21 :
      H.x.coeff 0 * H.d.coeff 0 -
        H.r.coeff 0 * H.r.coeff 0 = 0)
    (hcross :
      H.p.coeff 0 * H.d.coeff 0 -
        H.b.coeff 0 * H.r.coeff 0 ≠ 0) :
    H.shear02.activeDet.coeff 0 ≠ 0 := by
  rw [shear02_activeDet_coeff_zero, h01, h21]
  simp only [zero_add, add_zero]
  exact mul_ne_zero (by norm_num) hcross

/-! ## Generic exact-block Schur exhaustion -/

/-- The blocker Schur/zero-Schur split only needs an exact four-block clock
and a nonzero active constant minor.  This formulation is deliberately
independent of how the block was obtained, so determinant-preserving shears
can reuse the already-green Schur machinery directly. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.schur_or_zeroSchur_of_exactBlock
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (H : GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K)))
    (hdefect : 0 < B.aligned.endpoint.defect)
    (hfull :
      H.determinantCore =
        Polynomial.X ^ B.aligned.endpoint.defect)
    (hactive : H.activeDet.coeff 0 ≠ 0) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty
        (ExactZeroSchurFourBlockData
          (MvPolynomial (Fin 4) K)) := by
  by_cases hzero :
      H.schurA.coeff 0 = 0 ∧
        H.schurB.coeff 0 = 0 ∧
        H.schurC.coeff 0 = 0
  · right
    exact
      ⟨{
        block := H
        defect := B.aligned.endpoint.defect
        fullDet := hfull
        activeDet_coeff_zero_ne_zero := hactive
        schurA_coeff_zero := hzero.1
        schurB_coeff_zero := hzero.2.1
        schurC_coeff_zero := hzero.2.2
      }⟩
  · left
    have hnz : H.polynomialSchurSeries.ConstantBlockNonzero := by
      unfold BinarySchurPolynomialSeries.ConstantBlockNonzero
      simp only [GeneralFourBlock.polynomialSchurSeries]
      tauto

    have hdet :
        H.polynomialSchurSeries.determinant =
          H.activeDet *
            Polynomial.X ^ B.aligned.endpoint.defect := by
      calc
        H.polynomialSchurSeries.determinant =
            H.activeDet * H.determinantCore :=
          H.polynomialSchurSeries_determinant
        _ = H.activeDet *
            Polynomial.X ^ B.aligned.endpoint.defect := by
          rw [hfull]

    have hcoeff := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff 0)
      hdet

    have hne : B.aligned.endpoint.defect ≠ 0 :=
      Nat.ne_of_gt hdefect

    have hdet0 :
        H.schurA.coeff 0 * H.schurC.coeff 0 -
          H.schurB.coeff 0 * H.schurB.coeff 0 = 0 := by
      simpa [GeneralFourBlock.polynomialSchurSeries,
        BinarySchurPolynomialSeries.determinant,
        Polynomial.coeff_zero_eq_eval_zero, hne] using hcoeff

    have hdetEq :
        H.polynomialSchurSeries.active.coeff 0 *
            H.polynomialSchurSeries.kernel.coeff 0 =
          H.polynomialSchurSeries.offDiag.coeff 0 *
            H.polynomialSchurSeries.offDiag.coeff 0 := by
      have heq :
          H.schurA.coeff 0 * H.schurC.coeff 0 =
            H.schurB.coeff 0 * H.schurB.coeff 0 :=
        sub_eq_zero.mp hdet0
      simpa [GeneralFourBlock.polynomialSchurSeries] using heq

    have hpivot :
        H.polynomialSchurSeries.LeftPivot ∨
          H.polynomialSchurSeries.RightAxisPivot :=
      H.polynomialSchurSeries.leftPivot_or_rightAxisPivot_of_constantBlock
        hnz hdetEq

    exact
      ⟨{
        block := H
        fullDet := hfull
        activeDet_coeff_zero_ne_zero := hactive
        rigid := hpivot
      }⟩

/-! ## Honest recentered shear chart -/

/-- Apply the fixed determinant-one `e₀ ↦ e₀ + e₂` block shear after an
arbitrary coordinate permutation of the honest recentered Hessian. -/
noncomputable def adaptiveAlignedEndpointRightRecenteredHessianShear02FourBlock
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    GeneralFourBlock
      (Polynomial (MvPolynomial (Fin 4) K)) :=
  (adaptiveAlignedEndpointRightRecenteredHessianFourBlock rho E).shear02

/-- The exact Hessian determinant clock survives the block shear literally. -/
theorem adaptiveAlignedEndpointRightRecenteredHessianShear02FourBlock_determinantCore
    {degreeCap : ℕ}
    (rho : Equiv.Perm (Fin 4))
    (E : AdaptiveAlignedSmithMinimalEndpoint
      (K := K) degreeCap) :
    (adaptiveAlignedEndpointRightRecenteredHessianShear02FourBlock
      rho E).determinantCore =
      Polynomial.X ^ E.defect := by
  unfold adaptiveAlignedEndpointRightRecenteredHessianShear02FourBlock
  rw [GeneralFourBlock.shear02_determinantCore]
  exact
    adaptiveAlignedEndpointRightRecenteredHessianFourBlock_determinantCore
      rho E

/-- **Cross-minor escape from the coordinate-principal degenerate branch.**

For any coordinate ordering, if the `(0,1)` and `(2,1)` principal minors of
the constant recentered Hessian vanish but the corresponding cross minor is
nonzero, the elementary shear exposes a nonzero active chart.  Hence the
blocker immediately enters one of the two already-green Schur architectures.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredShear02Schur_or_zeroSchur_of_cross
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (rho : Equiv.Perm (Fin 4))
    (hdefect : 0 < B.aligned.endpoint.defect)
    (h01 :
      (adaptiveAlignedEndpointRightRecenteredHessianFourBlock
        rho B.aligned.endpoint).activeDet.coeff 0 = 0)
    (h21 :
      let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
        rho B.aligned.endpoint
      H.x.coeff 0 * H.d.coeff 0 -
        H.r.coeff 0 * H.r.coeff 0 = 0)
    (hcross :
      let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
        rho B.aligned.endpoint
      H.p.coeff 0 * H.d.coeff 0 -
        H.b.coeff 0 * H.r.coeff 0 ≠ 0) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty
        (ExactZeroSchurFourBlockData
          (MvPolynomial (Fin 4) K)) := by
  let H := adaptiveAlignedEndpointRightRecenteredHessianFourBlock
    rho B.aligned.endpoint
  let Hs := adaptiveAlignedEndpointRightRecenteredHessianShear02FourBlock
    rho B.aligned.endpoint

  have hactive : Hs.activeDet.coeff 0 ≠ 0 := by
    dsimp [Hs, adaptiveAlignedEndpointRightRecenteredHessianShear02FourBlock]
    apply shear02_activeDet_coeff_zero_ne_zero_of_cross
    · simpa [H] using h01
    · simpa [H] using h21
    · simpa [H] using hcross

  have hfull :
      Hs.determinantCore =
        Polynomial.X ^ B.aligned.endpoint.defect := by
    dsimp [Hs]
    exact
      adaptiveAlignedEndpointRightRecenteredHessianShear02FourBlock_determinantCore
        rho B.aligned.endpoint

  exact B.schur_or_zeroSchur_of_exactBlock
    Hs hdefect hfull hactive

end

end HC4.Valuation
