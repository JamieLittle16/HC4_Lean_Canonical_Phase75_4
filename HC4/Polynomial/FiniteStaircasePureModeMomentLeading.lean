import HC4.Polynomial.FiniteStaircasePureModeMixedDeterminant
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.HighestBinomialParallelFirstVariation
import Mathlib.Tactic

/-!
# Leading longitudinal coefficients of pure staircase moment Hessians

The mixed-core factorizations are numerical.  This file connects them to the
actual polynomial moment matrices used by the source-honest first-variation
pipeline.

For a pure profile `u X^m`, the coefficient of `X^m` in the parallel staircase
moment Hessian is exactly `u` times the exponent Hessian core of the literal
source exponent at longitudinal index `m`.

We also record the leading `X` coefficients of the locked and primitive-highest
binomial moment Hessians.  These are the four matrices appearing in the two
pure-mode mixed determinant factorizations.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Literal field-valued exponent of a parallel staircase fibre at
longitudinal index `m`. -/
def parallelStaircaseExponentAt
    (V k j m : ℕ) : Fin 4 → K :=
  ![(m : K), ((k - m : ℕ) : K), ((j + 1 - m : ℕ) : K),
    ((V * (k + j - m) : ℕ) : K)]

/-- The top longitudinal coefficient of a pure-mode parallel staircase moment
matrix is its scalar coefficient times the literal exponent Hessian core. -/
theorem coeff_parallelStaircaseMomentHessian_monomial
    (V k j m : ℕ)
    (hmk : m ≤ k) (hmj : m ≤ j + 1)
    (a : K) :
    (fun r s =>
      (parallelStaircaseMomentHessian V k j
        (Polynomial.monomial m a) r s).coeff m) =
      a • fieldExponentHessianCore (parallelStaircaseExponentAt V k j m) := by
  have hmKJ : m ≤ k + j := by omega
  apply Matrix.ext
  intro r s
  rw [coeff_rankThreeAffinePolynomialMomentHessian]
  simp only [Polynomial.coeff_monomial, if_pos]
  rw [Nat.cast_sub hmk, Nat.cast_sub hmj, Nat.cast_sub hmKJ]
  push_cast
  fin_cases r <;> fin_cases s <;>
    simp [parallelStaircaseMomentHessian, parallelStaircaseExponentAt,
      fieldExponentHessianCore, rankThreeLogBaseExponent,
      rankThreeLogDirection] <;> ring

/-- Leading longitudinal coefficient of the locked binomial moment Hessian. -/
theorem coeff_one_lockedBinomialMomentHessian
    (V ell : ℕ) (a b : K) :
    (fun r s => (lockedBinomialMomentHessian V ell a b r s).coeff 1) =
      b • fieldExponentHessianCore
        ![(1 : K), 0, (ell : K), (V : K) * (ell : K)] := by
  apply Matrix.ext
  intro r s
  rw [coeff_rankThreeAffinePolynomialMomentHessian]
  fin_cases r <;> fin_cases s <;>
    simp [lockedBinomialMomentHessian, fieldExponentHessianCore,
      rankThreeLogBaseExponent, rankThreeLogDirection] <;> ring

/-- Leading longitudinal coefficient of the primitive-highest binomial moment
Hessian. -/
theorem coeff_one_highestBinomialMomentHessian
    (V n : ℕ) (c d : K) :
    (fun r s => (highestBinomialMomentHessian V n c d r s).coeff 1) =
      d • fieldExponentHessianCore
        ![(1 : K), ((n - 1 : ℕ) : K), 0,
          (V : K) * ((n - 1 : ℕ) : K)] := by
  have hn : 1 ≤ n ∨ n = 0 := by omega
  apply Matrix.ext
  intro r s
  rw [coeff_rankThreeAffinePolynomialMomentHessian]
  rcases hn with hn | rfl
  · rw [Nat.cast_sub hn]
    fin_cases r <;> fin_cases s <;>
      simp [highestBinomialMomentHessian, fieldExponentHessianCore,
        rankThreeLogBaseExponent, rankThreeLogDirection] <;> ring
  · fin_cases r <;> fin_cases s <;>
      simp [highestBinomialMomentHessian, fieldExponentHessianCore,
        rankThreeLogBaseExponent, rankThreeLogDirection]

/-- Lower pure mode `j+2=k`, `m=k-1`: its leading exponent is
`(k-1,1,0,V(k-1))`. -/
theorem coeff_lowerPureMode_parallelStaircase
    (V k : ℕ) (hk : 2 ≤ k) (a : K) :
    (fun r s =>
      (parallelStaircaseMomentHessian V k (k - 2)
        (Polynomial.monomial (k - 1) a) r s).coeff (k - 1)) =
      a • fieldExponentHessianCore
        ![((k - 1 : ℕ) : K), 1, 0,
          (V : K) * ((k - 1 : ℕ) : K)] := by
  have hmk : k - 1 ≤ k := by omega
  have hmj : k - 1 ≤ (k - 2) + 1 := by omega
  have h := coeff_parallelStaircaseMomentHessian_monomial
    (K := K) V k (k - 2) (k - 1) hmk hmj a
  have hV :
      ((V * (k + (k - 2) - (k - 1)) : ℕ) : K) =
        (V : K) * ((k - 1 : ℕ) : K) := by
    congr 1
    omega
  simpa [parallelStaircaseExponentAt, hV] using h

/-- Upper pure mode `j=k`, `m=k`: its leading exponent is `(k,0,1,Vk)`. -/
theorem coeff_upperPureMode_parallelStaircase
    (V k : ℕ) (a : K) :
    (fun r s =>
      (parallelStaircaseMomentHessian V k k
        (Polynomial.monomial k a) r s).coeff k) =
      a • fieldExponentHessianCore
        ![(k : K), 0, 1, (V : K) * (k : K)] := by
  have h := coeff_parallelStaircaseMomentHessian_monomial
    (K := K) V k k k (by omega) (by omega) a
  have hV :
      ((V * (k + k - k) : ℕ) : K) = (V : K) * (k : K) := by
    push_cast
    ring
  simpa [parallelStaircaseExponentAt, hV] using h

end

end HC4.Polynomial
