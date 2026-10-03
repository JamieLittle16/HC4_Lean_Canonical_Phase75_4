import HC4.Polynomial.LockedBinomialFirstVariationRigidity
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Affine locked-binomial first-variation rigidity

The canonical Euler equation from `LockedBinomialFirstVariationRigidity` is
written after normalising the locked linear factor to `X`.  In the source
coordinates the factor is an arbitrary nonconstant affine polynomial

    L = A + B X,   B != 0.

The first-variation equation is

    L^2 phi'' + 2 B (1-k) L phi' + B^2 k(k-1) phi = 0.

The affine change `X |-> (X-A)/B` sends `L` to `X`, so the canonical two-root
classification applies.  Undoing the change gives the exact developable
normal form

    phi = c L^(k-1) + d L^k.

This file is state-free; it only packages the polynomial algebra needed by the
A19 first-positive-layer adapter.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The nonconstant affine factor carried by the locked binomial. -/
def lockedBinomialAffineFactor (A B : K) : Polynomial K :=
  Polynomial.C A + Polynomial.C B * Polynomial.X

/-- Inverse affine substitution sending `A + B X` to `X`. -/
def lockedBinomialAffineNormalize (A B : K) : Polynomial K :=
  Polynomial.C (-A * B⁻¹) + Polynomial.C B⁻¹ * Polynomial.X

/-- Source-coordinate first-variation operator. -/
def lockedBinomialAffineFirstVariationResidual
    (k : ℕ) (A B : K) (phi : Polynomial K) : Polynomial K :=
  (lockedBinomialAffineFactor A B) ^ 2 * phi.derivative.derivative +
    Polynomial.C (2 * B * (1 - (k : K))) *
      lockedBinomialAffineFactor A B * phi.derivative +
    Polynomial.C (B ^ 2 * (k : K) * ((k : K) - 1)) * phi

/-- Derivative form of the canonical Euler residual. -/
theorem lockedBinomialFirstVariationEulerResidual_eq_derivative_form
    (k : ℕ) (phi : Polynomial K) :
    lockedBinomialFirstVariationEulerResidual k phi =
      Polynomial.X ^ 2 * phi.derivative.derivative +
        Polynomial.C (2 * (1 - (k : K))) *
          Polynomial.X * phi.derivative +
        Polynomial.C ((k : K) * ((k : K) - 1)) * phi := by
  unfold lockedBinomialFirstVariationEulerResidual eulerDerivative
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X]
  ring

/-- The inverse affine substitution really sends the locked factor to `X`. -/
theorem lockedBinomialAffineFactor_comp_normalize
    (A B : K) (hB : B ≠ 0) :
    (lockedBinomialAffineFactor A B).comp
        (lockedBinomialAffineNormalize A B) = Polynomial.X := by
  unfold lockedBinomialAffineFactor lockedBinomialAffineNormalize
  simp only [Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp]
  have hBinv : B * B⁻¹ = 1 := mul_inv_cancel₀ hB
  rw [← Polynomial.C_mul, hBinv]
  simp
  ring

/-- Conversely, composing the normalising affine map with the original factor
is the identity. -/
theorem lockedBinomialAffineNormalize_comp_factor
    (A B : K) (hB : B ≠ 0) :
    (lockedBinomialAffineNormalize A B).comp
        (lockedBinomialAffineFactor A B) = Polynomial.X := by
  unfold lockedBinomialAffineFactor lockedBinomialAffineNormalize
  simp only [Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp]
  have hBinv : B⁻¹ * B = 1 := inv_mul_cancel₀ hB
  rw [← Polynomial.C_mul, hBinv]
  simp
  have hAB : A * B⁻¹ * B = A := by
    rw [mul_assoc, hBinv, mul_one]
  rw [← Polynomial.C_mul]
  simp [hAB]
  ring

/-- First derivative under the inverse affine substitution. -/
theorem derivative_comp_lockedBinomialAffineNormalize
    (A B : K) (phi : Polynomial K) :
    (phi.comp (lockedBinomialAffineNormalize A B)).derivative =
      Polynomial.C B⁻¹ *
        phi.derivative.comp (lockedBinomialAffineNormalize A B) := by
  rw [Polynomial.derivative_comp]
  unfold lockedBinomialAffineNormalize
  simp
  ring

/-- Second derivative under the same affine substitution. -/
theorem secondDerivative_comp_lockedBinomialAffineNormalize
    (A B : K) (phi : Polynomial K) :
    (phi.comp (lockedBinomialAffineNormalize A B)).derivative.derivative =
      Polynomial.C (B⁻¹ ^ 2) *
        phi.derivative.derivative.comp
          (lockedBinomialAffineNormalize A B) := by
  rw [derivative_comp_lockedBinomialAffineNormalize]
  rw [Polynomial.derivative_mul]
  simp only [Polynomial.derivative_C, zero_mul, zero_add]
  rw [Polynomial.derivative_comp]
  unfold lockedBinomialAffineNormalize
  simp
  ring

/-- Affine covariance of the first-variation equation.  The source residual
becomes `B^2` times the canonical Euler residual. -/
theorem lockedBinomialAffineFirstVariationResidual_comp_normalize
    (k : ℕ) (A B : K) (hB : B ≠ 0) (phi : Polynomial K) :
    (lockedBinomialAffineFirstVariationResidual k A B phi).comp
        (lockedBinomialAffineNormalize A B) =
      Polynomial.C (B ^ 2) *
        lockedBinomialFirstVariationEulerResidual k
          (phi.comp (lockedBinomialAffineNormalize A B)) := by
  let S := lockedBinomialAffineNormalize A B
  have hL : (lockedBinomialAffineFactor A B).comp S = Polynomial.X := by
    simpa [S] using lockedBinomialAffineFactor_comp_normalize A B hB
  have hD1 := derivative_comp_lockedBinomialAffineNormalize A B phi
  have hD2 := secondDerivative_comp_lockedBinomialAffineNormalize A B phi
  have hBinv : B * B⁻¹ = 1 := mul_inv_cancel₀ hB
  have hB2inv : B ^ 2 * B⁻¹ ^ 2 = 1 := by
    calc
      B ^ 2 * B⁻¹ ^ 2 = (B * B⁻¹) ^ 2 := by ring
      _ = 1 := by rw [hBinv]; norm_num
  rw [lockedBinomialFirstVariationEulerResidual_eq_derivative_form]
  unfold lockedBinomialAffineFirstVariationResidual
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.C_comp]
  rw [hL]
  rw [hD1, hD2]
  simp only [map_mul, map_pow]
  ring_nf
  rw [hBinv, hB2inv]
  ring

/-- A vanishing affine first variation therefore gives a vanishing canonical
Euler residual after normalisation. -/
theorem lockedBinomialFirstVariationEulerResidual_normalized_eq_zero
    (k : ℕ) (A B : K) (hB : B ≠ 0) (phi : Polynomial K)
    (hres : lockedBinomialAffineFirstVariationResidual k A B phi = 0) :
    lockedBinomialFirstVariationEulerResidual k
        (phi.comp (lockedBinomialAffineNormalize A B)) = 0 := by
  have hcov :=
    lockedBinomialAffineFirstVariationResidual_comp_normalize
      k A B hB phi
  rw [hres] at hcov
  simp only [Polynomial.zero_comp] at hcov
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hB
  have hC : Polynomial.C (B ^ 2) ≠ (0 : Polynomial K) :=
    Polynomial.C_ne_zero.mpr hB2
  exact (mul_eq_zero.mp hcov.symm).resolve_left hC

/-- **Affine two-root rigidity.**  Every polynomial solution of the actual
locked-binomial first-variation equation is a linear combination of the two
adjacent powers of the locked affine factor. -/
theorem eq_adjacent_lockedAffineFactor_powers_of_firstVariation_eq_zero
    (k : ℕ) (hk : 1 ≤ k) (A B : K) (hB : B ≠ 0)
    (phi : Polynomial K)
    (hres : lockedBinomialAffineFirstVariationResidual k A B phi = 0) :
    ∃ c d : K,
      phi =
        Polynomial.C c * (lockedBinomialAffineFactor A B) ^ (k - 1) +
          Polynomial.C d * (lockedBinomialAffineFactor A B) ^ k := by
  let S := lockedBinomialAffineNormalize A B
  let psi := phi.comp S
  have hcanon : lockedBinomialFirstVariationEulerResidual k psi = 0 := by
    dsimp [psi, S]
    exact lockedBinomialFirstVariationEulerResidual_normalized_eq_zero
      k A B hB phi hres
  have hshape :=
    eq_two_adjacent_terms_of_lockedBinomialFirstVariationEulerResidual_eq_zero
      k hk psi hcanon
  let c := psi.coeff (k - 1)
  let d := psi.coeff k
  refine ⟨c, d, ?_⟩
  have hcomp := congrArg
    (fun p : Polynomial K =>
      p.comp (lockedBinomialAffineFactor A B)) hshape
  have hSL := lockedBinomialAffineNormalize_comp_factor A B hB
  simpa [psi, S, c, d, Polynomial.comp_assoc, hSL] using hcomp

end

end HC4.Polynomial
