import HC4.Valuation.QuadraticTransverseCapSourceRiccatiLinearMatrix
import HC4.Valuation.QuadraticTransverseCapSourceLongitudinalDrift
import Mathlib.Tactic

/-!
# Mixed-vector source Riccati: affine reciprocal product ODE

The polynomial reciprocal M=C⁻¹ of the transverse Hessian has M''=0.
The source's linear Riccati equation and the derivative of M*C=1
then imply (M*b)''=0, where b is the actual transverse-linear
coefficient vector of the source.

The first theorem isolates the polynomial matrix/vector calculus;
source transport and the marked collision are handled separately.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton
variable {K : Type*} [Field K] [CharZero K]

/-- Algebraic mixed-vector ODE consequence: if M''=0,
M'=-M P M, and b''=2(P M)b', then (M b)''=0. -/
theorem quadraticTransverse_affineInverse_linearODE_productSecond_zero
    (M P : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (b : Fin 3 → Polynomial K)
    (hMsecond :
      quadraticTransverse_polynomialMatrixDerivative
        (quadraticTransverse_polynomialMatrixDerivative M) = 0)
    (hMprime :
      quadraticTransverse_polynomialMatrixDerivative M = -(M * P * M))
    (hlinear :
      quadraticTransverse_polynomialVectorDerivative
          (quadraticTransverse_polynomialVectorDerivative b) =
        (P * M).mulVec (quadraticTransverse_polynomialVectorDerivative b) +
          (P * M).mulVec (quadraticTransverse_polynomialVectorDerivative b)) :
    ∀ i : Fin 3,
      Polynomial.derivative (Polynomial.derivative (M.mulVec b i)) = 0 := by
  let δ := quadraticTransverse_polynomialVectorDerivative (K := K)
  let D := quadraticTransverse_polynomialMatrixDerivative (K := K)
  let v := δ b
  have hmul (A : Matrix (Fin 3) (Fin 3) (Polynomial K))
      (w : Fin 3 → Polynomial K) :
      δ (A.mulVec w) = (D A).mulVec w + A.mulVec (δ w) :=
    quadraticTransverse_polynomialVectorDerivative_mulVec A w
  have hadd (w z : Fin 3 → Polynomial K) :
      δ (w + z) = δ w + δ z :=
    quadraticTransverse_polynomialVectorDerivative_add w z
  have hMsecond' : D (D M) = 0 := hMsecond
  have hMprime' : D M = -(M * P * M) := hMprime
  have hlinear' :
      δ v = (P * M).mulVec v + (P * M).mulVec v := hlinear
  have hproduct :
      δ (δ (M.mulVec b)) =
        (D (D M)).mulVec b + (D M).mulVec v +
          ((D M).mulVec v + M.mulVec (δ v)) := by
    calc
      δ (δ (M.mulVec b)) =
          δ ((D M).mulVec b + M.mulVec v) := by
            rw [hmul M b]
      _ = (D (D M)).mulVec b + (D M).mulVec v +
          ((D M).mulVec v + M.mulVec (δ v)) := by
            rw [hadd, hmul, hmul]
  have hzero : δ (δ (M.mulVec b)) = 0 := by
    rw [hproduct, hMsecond', Matrix.zero_mulVec, zero_add, hlinear']
    simp only [hMprime', Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.neg_mulVec, Matrix.mul_assoc]
    abel
  intro i
  have hi := congrFun hzero i
  simpa only [δ, quadraticTransverse_polynomialVectorDerivative,
    Pi.zero_apply] using hi

/-- Derivative of the polynomial matrix inverse, with exact order
of the noncommuting factors. -/
theorem quadraticTransverse_polynomialInverse_derivative
    (C M : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (hCM : C * M = 1)
    (hMC : M * C = 1) :
    quadraticTransverse_polynomialMatrixDerivative M =
      -(M * quadraticTransverse_polynomialMatrixDerivative C * M) := by
  let D := quadraticTransverse_polynomialMatrixDerivative (K := K)
  have hone : D (1 : Matrix (Fin 3) (Fin 3) (Polynomial K)) = 0 := by
    apply Matrix.ext
    intro i j
    change Polynomial.derivative
      (if i = j then (1 : Polynomial K) else 0) = 0
    split_ifs <;> simp
  have hproduct : D M * C + M * D C = 0 := by
    calc
      D M * C + M * D C = D (M * C) :=
        (quadraticTransverse_polynomialMatrixDerivative_mul M C).symm
      _ = D 1 := congrArg D hMC
      _ = 0 := hone
  have hneg : D M * C = -(M * D C) :=
    eq_neg_of_add_eq_zero_left hproduct
  calc
    D M = (D M * C) * M := by
      rw [mul_assoc, hCM, mul_one]
    _ = -(M * D C) * M := by rw [hneg]
    _ = -(M * D C * M) := by noncomm_ring

end
end HC4.Valuation
