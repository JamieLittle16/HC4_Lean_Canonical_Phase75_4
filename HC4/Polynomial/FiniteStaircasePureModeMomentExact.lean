import HC4.Polynomial.FiniteStaircasePureModeMomentLeading
import Mathlib.Tactic

/-!
# Exact moment matrices of pure affine staircase modes

For a one-term coefficient profile `a X^m`, every Euler moment has the same
monomial factor.  Consequently the complete rank-three affine moment Hessian
is exactly

    (a X^m) * M(e_m),

where `M(e_m)` is the constant exponent Hessian core of the literal exponent
at longitudinal index `m`.

This exact factorisation is stronger than the leading-coefficient bridge and
is the convenient input for the remaining quadratic/cubic determinant
variation.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Generic pure affine-line profile gives a scalar polynomial multiple of its
literal exponent Hessian core. -/
theorem rankThreeAffineMomentHessian_monomial_eq
    (A B C u1 m : ℕ) (q r s : K) (a : K) :
    rankThreeAffinePolynomialMomentHessian
        A B C u1 q r s (Polynomial.monomial m a) =
      (Polynomial.monomial m a) •
        fieldExponentHessianCore
          (fun i =>
            rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
              (m : K) * rankThreeLogDirection (u1 : K) q r s i) := by
  apply Matrix.ext
  intro i j
  rw [rankThreeAffinePolynomialMomentHessian_apply]
  have hE1 :
      eulerDerivative (Polynomial.monomial m a) =
        Polynomial.monomial m ((m : K) * a) := by
    apply Polynomial.ext
    intro n
    simp [coeff_eulerDerivative, Polynomial.coeff_monomial]
    by_cases hnm : n = m
    · subst n
      ring
    · simp [hnm]
  have hE2 :
      eulerDerivative (eulerDerivative (Polynomial.monomial m a)) =
        Polynomial.monomial m ((m : K) ^ 2 * a) := by
    rw [hE1]
    apply Polynomial.ext
    intro n
    simp [coeff_eulerDerivative, Polynomial.coeff_monomial]
    by_cases hnm : n = m
    · subst n
      ring
    · simp [hnm]
  rw [hE1, hE2]
  by_cases hij : i = j
  · subst j
    simp [fieldExponentHessianCore]
    ring
  · simp [fieldExponentHessianCore, hij]
    ring

/-- Exact pure-mode form for a parallel staircase fibre. -/
theorem parallelStaircaseMomentHessian_monomial_eq
    (V k j m : ℕ) (a : K) :
    parallelStaircaseMomentHessian V k j (Polynomial.monomial m a) =
      (Polynomial.monomial m a) •
        fieldExponentHessianCore
          (fun i =>
            rankThreeLogBaseExponent
                (k : K) ((j + 1 : ℕ) : K) ((V * (k + j) : ℕ) : K) i +
              (m : K) *
                rankThreeLogDirection (1 : K) (-1 : K) (-1 : K)
                  (-(V : K)) i) := by
  exact rankThreeAffineMomentHessian_monomial_eq
    k (j + 1) (V * (k + j)) 1 m
    (-1 : K) (-1 : K) (-(V : K)) a

/-- Lower pure mode simplifies to the literal exponent
`(k-1,1,0,V(k-1))`. -/
theorem lowerPureMode_parallelStaircaseMomentHessian_eq
    (V k : ℕ) (hk : 2 ≤ k) (a : K) :
    parallelStaircaseMomentHessian V k (k - 2)
        (Polynomial.monomial (k - 1) a) =
      (Polynomial.monomial (k - 1) a) •
        fieldExponentHessianCore
          ![((k - 1 : ℕ) : K), 1, 0,
            (V : K) * ((k - 1 : ℕ) : K)] := by
  have h := parallelStaircaseMomentHessian_monomial_eq
    (K := K) V k (k - 2) (k - 1) a
  rw [h]
  congr 1
  funext i
  fin_cases i <;>
    simp [rankThreeLogBaseExponent, rankThreeLogDirection] <;>
    push_cast <;> ring

/-- Upper pure mode simplifies to `(k,0,1,Vk)`. -/
theorem upperPureMode_parallelStaircaseMomentHessian_eq
    (V k : ℕ) (a : K) :
    parallelStaircaseMomentHessian V k k
        (Polynomial.monomial k a) =
      (Polynomial.monomial k a) •
        fieldExponentHessianCore
          ![(k : K), 0, 1, (V : K) * (k : K)] := by
  have h := parallelStaircaseMomentHessian_monomial_eq
    (K := K) V k k k a
  rw [h]
  congr 1
  funext i
  fin_cases i <;>
    simp [rankThreeLogBaseExponent, rankThreeLogDirection] <;>
    push_cast <;> ring

end

end HC4.Polynomial
