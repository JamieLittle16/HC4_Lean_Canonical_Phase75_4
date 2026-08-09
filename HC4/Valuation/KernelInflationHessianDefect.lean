import HC4.Valuation.ConcreteIntegralKernelRestart
import HC4.Polynomial.HessianDeterminant
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Kernel inflation and the Hessian determinant defect

Phases 93.52--93.55 constructed the integral kernel blow-up

    Ptilde(X,T) = P(X, tau^(-q) T)

without ever leaving the polynomial ring, and proved exact collision
covariance.

This file formalises the determinant calculation that was still missing.

Rather than introducing negative powers, define the honest polynomial
substitution

    Inflate_q : T |-> tau^q T,

fixing every other source variable and every coefficient in `K[tau]`.

For the explicitly reconstructed integral blow-up, we prove

    Inflate_q(Ptilde) = P.

The formal chain rule then gives one factor `tau^q` for each Hessian
row/column in the kernel direction, hence exactly two factors in the
determinant:

    det Hess(Inflate_q Q)
      =
    tau^(2q) * Inflate_q(det Hess Q).

Applying this to `Q = Ptilde` yields the exact reinflated determinant
identity needed for the defect update.
-/

namespace HC4.Valuation

noncomputable section

open scoped BigOperators

variable {K : Type*} [Field K]

/-! ## The inflation substitution -/

/-- Coefficient factor attached to one source variable by kernel inflation. -/
def kernelInflateDerivativeCoefficient
    (kernel : Fin 4)
    (slope : ℕ)
    (i : Fin 4) :
    Polynomial K :=
  if i = kernel then
    Polynomial.X ^ slope
  else
    1

/-- Image of one source variable under kernel inflation. -/
def kernelInflateVariable
    (kernel : Fin 4)
    (slope : ℕ)
    (i : Fin 4) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.C
      (kernelInflateDerivativeCoefficient
        (K := K) kernel slope i) *
    MvPolynomial.X i

/-- The actual polynomial-ring substitution
`T |-> tau^slope T`, fixing the coefficient ring `K[tau]`. -/
noncomputable def kernelInflateHom
    (kernel : Fin 4)
    (slope : ℕ) :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.eval₂Hom
    MvPolynomial.C
    (kernelInflateVariable (K := K) kernel slope)

/-- The point transformation from Phase 93.52 is exactly multiplication by
the same diagonal coefficient factors used by `kernelInflateHom`. -/
theorem kernelBlowupSection_eq_factor_mul
    (kernel : Fin 4)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K) :
    kernelBlowupSection kernel slope a =
      fun i =>
        kernelInflateDerivativeCoefficient
            (K := K) kernel slope i * a i := by
  funext i
  by_cases hi : i = kernel
  · subst i
    simp [kernelBlowupSection,
      kernelInflateDerivativeCoefficient]
  · simp [kernelBlowupSection,
      kernelInflateDerivativeCoefficient, hi]

/-- Evaluation semantics of the inflation homomorphism. -/
theorem eval_kernelInflateHom
    (kernel : Fin 4)
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval a
        (kernelInflateHom (K := K) kernel slope Q) =
      MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        Q := by
  change
    MvPolynomial.eval a
        (MvPolynomial.eval₂
          MvPolynomial.C
          (kernelInflateVariable (K := K) kernel slope)
          Q) =
      MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        Q
  rw [← MvPolynomial.eval_assoc
    (kernelInflateVariable (K := K) kernel slope)
    a Q]
  apply congrArg (fun x =>
    MvPolynomial.eval x Q)
  funext i
  by_cases hi : i = kernel
  · subst i
    simp [kernelInflateVariable,
      kernelInflateDerivativeCoefficient,
      kernelBlowupSection]
  · simp [kernelInflateVariable,
      kernelInflateDerivativeCoefficient,
      kernelBlowupSection, hi]

/-- **Reinflation recovers the original family exactly.**

This identifies the explicit quotient construction of Phase 93.52 with the
honest substitution `T |-> tau^q T`. -/
theorem kernelInflate_integralKernelBlowupFamily_eq
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P) :
    kernelInflateHom (K := K) kernel slope
        (integralKernelBlowupFamily
          kernel slope P hdiv) =
      P := by
  apply MvPolynomial.funext
  intro a
  rw [eval_kernelInflateHom]
  exact
    eval_integralKernelBlowupFamily_kernelBlowupSection
      kernel slope P hdiv a

/-! ## Formal chain rule -/

/-- **First-order chain rule for kernel inflation.**

Every source derivative acquires its diagonal chain-rule coefficient.
Only the kernel direction contributes a nontrivial factor `tau^slope`. -/
theorem pderiv_kernelInflateHom
    (kernel i : Fin 4)
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial.pderiv i
        (kernelInflateHom (K := K) kernel slope Q) =
      MvPolynomial.C
          (kernelInflateDerivativeCoefficient
            (K := K) kernel slope i) *
        kernelInflateHom (K := K) kernel slope
          (MvPolynomial.pderiv i Q) := by
  apply MvPolynomial.induction_on Q
  · intro c
    simp [kernelInflateHom]
  · intro p q hp hq
    simp [hp, hq, mul_add]
  · intro p n hp
    have hp' :
        MvPolynomial.pderiv i
            (MvPolynomial.bind₁
              (kernelInflateVariable (K := K) kernel slope) p) =
          MvPolynomial.C
              (kernelInflateDerivativeCoefficient
                (K := K) kernel slope i) *
            MvPolynomial.bind₁
              (kernelInflateVariable (K := K) kernel slope)
              (MvPolynomial.pderiv i p) := by
      simpa [kernelInflateHom] using hp
    by_cases hni : n = i
    · subst n
      simp [kernelInflateHom, kernelInflateVariable,
        hp']
      ring
    · have hin : i ≠ n := Ne.symm hni
      simp [kernelInflateHom, kernelInflateVariable,
        hp', hni, hin]
      ring

/-- Entrywise Hessian chain rule. -/
theorem hessian_kernelInflateHom_entry
    (kernel : Fin 4)
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessian
        (kernelInflateHom (K := K) kernel slope Q) i j =
      MvPolynomial.C
          (kernelInflateDerivativeCoefficient
            (K := K) kernel slope i) *
        MvPolynomial.C
          (kernelInflateDerivativeCoefficient
            (K := K) kernel slope j) *
        kernelInflateHom (K := K) kernel slope
          (HC4.Polynomial.hessian Q i j) := by
  rw [HC4.Polynomial.hessian_apply]
  rw [pderiv_kernelInflateHom
    kernel i slope Q]
  rw [MvPolynomial.pderiv_C_mul]
  rw [pderiv_kernelInflateHom
    kernel j slope (MvPolynomial.pderiv i Q)]
  rw [HC4.Polynomial.hessian_apply]
  ring

/-- There is exactly one nontrivial diagonal chain-rule factor. -/
theorem prod_kernelInflateDerivativeCoefficient
    (kernel : Fin 4)
    (slope : ℕ) :
    (∏ i : Fin 4,
      (MvPolynomial.C
        (kernelInflateDerivativeCoefficient
          (K := K) kernel slope i) :
        MvPolynomial (Fin 4) (Polynomial K))) =
      (MvPolynomial.C
        (Polynomial.X ^ slope) :
        MvPolynomial (Fin 4) (Polynomial K)) := by
  fin_cases kernel <;>
    simp [kernelInflateDerivativeCoefficient,
      Fin.prod_univ_four]

/-! ## Hessian determinant scaling -/

/-- **Exact Hessian determinant scaling under kernel inflation.**

The single kernel chain-rule factor occurs once among the rows and once
among the columns, so the determinant gains exactly `tau^(2*slope)`. -/
theorem hessianDeterminant_kernelInflateHom
    (kernel : Fin 4)
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    HC4.Polynomial.hessianDeterminant
        (kernelInflateHom (K := K) kernel slope Q) =
      (MvPolynomial.C
        (Polynomial.X ^ slope)) ^ 2 *
        kernelInflateHom (K := K) kernel slope
          (HC4.Polynomial.hessianDeterminant Q) := by
  let v : Fin 4 →
      MvPolynomial (Fin 4) (Polynomial K) :=
    fun i =>
      MvPolynomial.C
        (kernelInflateDerivativeCoefficient
          (K := K) kernel slope i)
  let A : Matrix (Fin 4) (Fin 4)
      (MvPolynomial (Fin 4) (Polynomial K)) :=
    (kernelInflateHom (K := K) kernel slope).mapMatrix
      (HC4.Polynomial.hessian Q)
  have hmatrix :
      HC4.Polynomial.hessian
          (kernelInflateHom (K := K) kernel slope Q) =
        fun i j => v i * (v j * A i j) := by
    apply Matrix.ext
    intro i j
    simpa [v, A, mul_assoc] using
      (hessian_kernelInflateHom_entry
        (K := K) kernel slope Q i j)
  have hv :
      (∏ i : Fin 4, v i) =
        MvPolynomial.C
          (Polynomial.X ^ slope) := by
    simpa [v] using
      (prod_kernelInflateDerivativeCoefficient
        (K := K) kernel slope)
  have hrow :
      (Matrix.det fun i j => v j * A i j) =
        (∏ i : Fin 4, v i) * A.det := by
    exact Matrix.det_mul_row v A
  have hmapdet :
      A.det =
        kernelInflateHom (K := K) kernel slope
          ((HC4.Polynomial.hessian Q).det) := by
    simpa [A] using
      (RingHom.map_det
        (kernelInflateHom (K := K) kernel slope)
        (HC4.Polynomial.hessian Q)).symm
  unfold HC4.Polynomial.hessianDeterminant
  rw [hmatrix]
  calc
    (Matrix.det fun i j => v i * (v j * A i j)) =
        (∏ i : Fin 4, v i) *
          (Matrix.det fun i j => v j * A i j) := by
      exact Matrix.det_mul_column
        v (fun i j => v j * A i j)
    _ =
        (∏ i : Fin 4, v i) *
          ((∏ i : Fin 4, v i) * A.det) := by
      rw [hrow]
    _ =
        (MvPolynomial.C
          (Polynomial.X ^ slope)) ^ 2 *
          A.det := by
      rw [hv]
      ring
    _ =
        (MvPolynomial.C
          (Polynomial.X ^ slope)) ^ 2 *
          kernelInflateHom (K := K) kernel slope
            ((HC4.Polynomial.hessian Q).det) := by
      rw [hmapdet]

/-- **Concrete determinant identity for the integral kernel blow-up.**

For the actual family `Ptilde` built in Phase 93.52,

    det Hess P
      =
    tau^(2q) * Inflate_q(det Hess Ptilde).

This is the determinant identity from which the numerical defect update
`Delta' = Delta - 2q` is extracted. -/
theorem hessianDeterminant_integralKernelBlowup_factor
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P) :
    HC4.Polynomial.hessianDeterminant P =
      (MvPolynomial.C
        (Polynomial.X ^ slope)) ^ 2 *
        kernelInflateHom (K := K) kernel slope
          (HC4.Polynomial.hessianDeterminant
            (integralKernelBlowupFamily
              kernel slope P hdiv)) := by
  have hreinflate :=
    kernelInflate_integralKernelBlowupFamily_eq
      kernel slope P hdiv
  calc
    HC4.Polynomial.hessianDeterminant P =
        HC4.Polynomial.hessianDeterminant
          (kernelInflateHom (K := K) kernel slope
            (integralKernelBlowupFamily
              kernel slope P hdiv)) := by
      rw [hreinflate]
    _ =
      (MvPolynomial.C
        (Polynomial.X ^ slope)) ^ 2 *
        kernelInflateHom (K := K) kernel slope
          (HC4.Polynomial.hessianDeterminant
            (integralKernelBlowupFamily
              kernel slope P hdiv)) :=
      hessianDeterminant_kernelInflateHom
        kernel slope
        (integralKernelBlowupFamily
          kernel slope P hdiv)

/-- Semantic statement that a polynomial family has pure parameter
Hessian-determinant defect `Delta`. -/
def HasPolynomialFamilyHessianDefect
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (Delta : ℕ) : Prop :=
  HC4.Polynomial.hessianDeterminant P =
    MvPolynomial.C (Polynomial.X ^ Delta)

/-- A source defect certificate gives the exact factored equation for the
target determinant. -/
theorem integralKernelBlowup_defect_factor_equation
    (kernel : Fin 4)
    (slope Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    MvPolynomial.C (Polynomial.X ^ Delta) =
      (MvPolynomial.C
        (Polynomial.X ^ slope)) ^ 2 *
        kernelInflateHom (K := K) kernel slope
          (HC4.Polynomial.hessianDeterminant
            (integralKernelBlowupFamily
              kernel slope P hdiv)) := by
  rw [← hdef]
  exact
    hessianDeterminant_integralKernelBlowup_factor
      kernel slope P hdiv

end

end HC4.Valuation
