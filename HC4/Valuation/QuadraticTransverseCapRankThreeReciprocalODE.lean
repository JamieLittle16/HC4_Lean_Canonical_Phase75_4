import HC4.Valuation.QuadraticTransverseCapRankThreeAffineInverse
import Mathlib.Tactic

/-!
# Rank-three Riccati equation forces the reciprocal matrix to be affine

For the generic rank-three quadratic transverse source, the
transverse-quadratic coefficient of det Hess F = 1 is the
matrix Riccati identity C'' = 2 C' C⁻¹ C'.

This file proves its exact *noncommutative matrix algebra* consequence,
without any assumption that C and C' commute:
  (C⁻¹)'' = 0.

We first work in matrices over K[x] when a polynomial two-sided inverse
exists. The same identity will subsequently be used in matrices over
the rational function field K(x) after establishing the derivative
transport there. The polynomial version also gives an exact affine
matrix conclusion with no analytical integration.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private def dmat
    (M : Matrix (Fin 3) (Fin 3) (Polynomial K)) :=
  quadraticTransverse_polynomialMatrixDerivative M

private theorem dmat_mul
    (M N : Matrix (Fin 3) (Fin 3) (Polynomial K)) :
    dmat (M * N) = dmat M * N + M * dmat N :=
  quadraticTransverse_polynomialMatrixDerivative_mul M N

private theorem dmat_neg
    (M : Matrix (Fin 3) (Fin 3) (Polynomial K)) :
    dmat (-M) = -dmat M := by
  ext i j
  simp [dmat, quadraticTransverse_polynomialMatrixDerivative]

private theorem dmat_one :
    dmat (1 : Matrix (Fin 3) (Fin 3) (Polynomial K)) = 0 := by
  ext i j
  simp [dmat, quadraticTransverse_polynomialMatrixDerivative,
    Matrix.one_apply]

/-- **Noncommutative reciprocal Riccati identity.**

Given an actual polynomial two-sided inverse M of a 3x3
polynomial matrix C, the Riccati equation

  C'' = 2 C' M C'

implies M''=0, even though M,C,C' need not commute.

The existence of a POLYNOMIAL inverse is a separate rank-three
source obligation; no such property is silently inferred from
generic nonvanishing of det C. -/
theorem quadraticTransverse_reciprocal_secondDerivative_zero
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCM : C * M = 1)
    (hMC : M * C = 1)
    (hRiccati :
      dmat (dmat C) = 2 * ((dmat C * M) * dmat C)) :
    dmat (dmat M) = 0 := by
  have hprod : dmat M * C + M * dmat C = 0 := by
    have h := congrArg dmat hMC
    rw [dmat_mul, dmat_one] at h
    exact h
  have hneg : dmat M * C = -(M * dmat C) := by
    exact eq_neg_of_add_eq_zero_left hprod
  have hMprime : dmat M = -((M * dmat C) * M) := by
    calc
      dmat M = (dmat M * C) * M := by
        rw [mul_assoc, hCM, mul_one]
      _ = (-(M * dmat C)) * M := by rw [hneg]
      _ = -((M * dmat C) * M) := by
        noncomm_ring
  calc
    dmat (dmat M) =
        -dmat ((M * dmat C) * M) := by
          rw [hMprime, dmat_neg]
    _ = -(((dmat M * dmat C + M * dmat (dmat C)) * M) +
        (M * dmat C) * dmat M) := by
          rw [dmat_mul, dmat_mul]
    _ = 0 := by
      rw [hMprime, hRiccati]
      noncomm_ring

/-- If the Riccati reciprocal matrix is already polynomial, the
vanishing second derivative gives an *actual affine matrix* over K,
not a merely formal or analytic normal form. -/
theorem quadraticTransverse_reciprocal_polynomial_affine
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCM : C * M = 1)
    (hMC : M * C = 1)
    (hRiccati :
      dmat (dmat C) = 2 * ((dmat C * M) * dmat C)) :
    ∃ A B : Matrix (Fin 3) (Fin 3) K,
      ∀ i j : Fin 3,
        M i j = Polynomial.C (A i j) +
          Polynomial.C (B i j) * Polynomial.X := by
  have hzero :=
    quadraticTransverse_reciprocal_secondDerivative_zero
      C M hCM hMC hRiccati
  apply quadraticTransverse_polynomialMatrix_secondDerivative_zero_affine M
  intro i j
  have h := congrArg (fun H : Matrix (Fin 3) (Fin 3) (Polynomial K) =>
      H i j) hzero
  exact h

end

end HC4.Valuation
