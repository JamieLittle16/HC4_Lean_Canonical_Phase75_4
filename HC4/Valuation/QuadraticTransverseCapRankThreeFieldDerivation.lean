import HC4.Valuation.QuadraticTransverseCapRankThreeReciprocalODE
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-!
# Rank-three reciprocal Riccati equation over a differential coefficient field

The already-written polynomial-matrix reciprocal lemma is not sufficient for
a source C(x) whose polynomial determinant is merely nonzero: the inverse
then lives in the rational-function field K(x).

This file removes that artificial polynomial-inverse hypothesis from the
MATRIX ALGEBRA. The derivative is an arbitrary K-linear derivation on a
commutative field L (later L = RatFunc K); matrix multiplication is
noncommutative and its derivative obeys the correct Leibniz rule.

The exact remaining rational-function issue is now independent of matrices:
construct the X-derivation on RatFunc K and show that its constants are
precisely the ground field K. With those facts the matrix reciprocal is
affine over K, without ever assuming polynomial invertibility.
-/

namespace HC4.Valuation

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Entrywise application of an arbitrary field derivation to a 3x3
matrix. Unlike polynomial-specific differentiation, this works for
genuinely rational matrix entries. -/
def quadraticTransverse_fieldMatrixDerivative
    (D : Derivation K L L)
    (M : Matrix (Fin 3) (Fin 3) L) :
    Matrix (Fin 3) (Fin 3) L :=
  fun i j => D (M i j)

/-- Exact noncommutative matrix product rule, with no assumption that
M and N commute. -/
theorem quadraticTransverse_fieldMatrixDerivative_mul
    (D : Derivation K L L)
    (M N : Matrix (Fin 3) (Fin 3) L) :
    quadraticTransverse_fieldMatrixDerivative D (M * N) =
      quadraticTransverse_fieldMatrixDerivative D M * N +
        M * quadraticTransverse_fieldMatrixDerivative D N := by
  ext i j
  change
    D (∑ k : Fin 3, M i k * N k j) =
      (∑ k : Fin 3, D (M i k) * N k j) +
        (∑ k : Fin 3, M i k * D (N k j))
  rw [map_sum]
  simp_rw [D.leibniz]
  simp only [smul_eq_mul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix differentiation commutes with negation. -/
theorem quadraticTransverse_fieldMatrixDerivative_neg
    (D : Derivation K L L)
    (M : Matrix (Fin 3) (Fin 3) L) :
    quadraticTransverse_fieldMatrixDerivative D (-M) =
      -quadraticTransverse_fieldMatrixDerivative D M := by
  ext i j
  simp [quadraticTransverse_fieldMatrixDerivative]

/-- The derivative of the constant identity matrix is zero. -/
theorem quadraticTransverse_fieldMatrixDerivative_one
    (D : Derivation K L L) :
    quadraticTransverse_fieldMatrixDerivative D
      (1 : Matrix (Fin 3) (Fin 3) L) = 0 := by
  ext i j
  simp [quadraticTransverse_fieldMatrixDerivative,
    Matrix.one_apply]

/-- **Reciprocal Riccati rigidity over ANY differential field.**

For a genuine rational inverse M=C⁻¹, the matrix identity
  C'' = 2 C' M C'
forces M''=0. No polynomial matrix inverse, no commutation between C
and C', and no analytic differentiation are assumed. -/
theorem quadraticTransverse_fieldReciprocal_secondDerivative_zero
    (D : Derivation K L L)
    (C M : Matrix (Fin 3) (Fin 3) L)
    (hCM : C * M = 1)
    (hMC : M * C = 1)
    (hRiccati :
      quadraticTransverse_fieldMatrixDerivative D
          (quadraticTransverse_fieldMatrixDerivative D C) =
        2 * ((quadraticTransverse_fieldMatrixDerivative D C * M) *
          quadraticTransverse_fieldMatrixDerivative D C)) :
    quadraticTransverse_fieldMatrixDerivative D
      (quadraticTransverse_fieldMatrixDerivative D M) = 0 := by
  let dd := quadraticTransverse_fieldMatrixDerivative D
  have hprod : dd M * C + M * dd C = 0 := by
    have h := congrArg dd hMC
    rw [quadraticTransverse_fieldMatrixDerivative_mul,
      quadraticTransverse_fieldMatrixDerivative_one] at h
    exact h
  have hneg : dd M * C = -(M * dd C) :=
    eq_neg_of_add_eq_zero_left hprod
  have hMprime : dd M = -((M * dd C) * M) := by
    calc
      dd M = (dd M) * (C * M) := by rw [hCM, mul_one]
      _ = ((dd M) * C) * M := by rw [mul_assoc]
      _ = (-(M * dd C)) * M := by rw [hneg]
      _ = -((M * dd C) * M) := by noncomm_ring
  calc
    dd (dd M) = -dd ((M * dd C) * M) := by
      rw [hMprime, quadraticTransverse_fieldMatrixDerivative_neg]
    _ = -(((dd M * dd C + M * dd (dd C)) * M) +
        (M * dd C) * dd M) := by
          rw [quadraticTransverse_fieldMatrixDerivative_mul,
            quadraticTransverse_fieldMatrixDerivative_mul]
    _ = 0 := by
      rw [hMprime, hRiccati]
      noncomm_ring

/-- If an arbitrary differential field has exactly K as its field
of constants, every element with zero second derivative is affine
in an element x satisfying D(x)=1.

In the eventual application x is the rational-function indeterminate,
and the constants-field condition is to be PROVED for RatFunc K. -/
theorem quadraticTransverse_field_secondDerivative_zero_affine
    (D : Derivation K L L)
    (x : L)
    (hx : D x = 1)
    (hconstants :
      ∀ z : L, D z = 0 → ∃ c : K, z = algebraMap K L c)
    (f : L)
    (hsecond : D (D f) = 0) :
    ∃ a b : K,
      f = algebraMap K L a + algebraMap K L b * x := by
  obtain ⟨b, hb⟩ := hconstants (D f) hsecond
  have hzero :
      D (f - algebraMap K L b * x) = 0 := by
    simp [D.leibniz, hb, hx, smul_eq_mul]
  obtain ⟨a, ha⟩ := hconstants
    (f - algebraMap K L b * x) hzero
  exact ⟨a, b, (sub_eq_iff_eq_add.mp ha)⟩

/-- Entrywise affine rigidity for a rational 3x3 reciprocal matrix,
once the rational derivation and constants-field theorem are provided.
Both coefficient matrices A and B live in the ORIGINAL ground field K. -/
theorem quadraticTransverse_fieldMatrix_secondDerivative_zero_affine
    (D : Derivation K L L)
    (x : L)
    (hx : D x = 1)
    (hconstants :
      ∀ z : L, D z = 0 → ∃ c : K, z = algebraMap K L c)
    (M : Matrix (Fin 3) (Fin 3) L)
    (hsecond :
      quadraticTransverse_fieldMatrixDerivative D
        (quadraticTransverse_fieldMatrixDerivative D M) = 0) :
    ∃ A B : Matrix (Fin 3) (Fin 3) K,
      ∀ i j : Fin 3,
        M i j = algebraMap K L (A i j) +
          algebraMap K L (B i j) * x := by
  classical
  have hex : ∀ i j : Fin 3, ∃ a b : K,
      M i j = algebraMap K L a + algebraMap K L b * x := by
    intro i j
    apply quadraticTransverse_field_secondDerivative_zero_affine
      D x hx hconstants (M i j)
    exact congrArg (fun H : Matrix (Fin 3) (Fin 3) L =>
      H i j) hsecond
  choose a b hab using hex
  exact ⟨(fun i j => a i j), (fun i j => b i j), hab⟩

end

end HC4.Valuation
