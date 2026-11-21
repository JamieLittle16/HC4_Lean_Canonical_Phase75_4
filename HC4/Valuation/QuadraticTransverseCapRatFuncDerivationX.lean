import HC4.Valuation.QuadraticTransverseCapRatFuncConstants
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Tactic

/-!
# The rational indeterminate's derivative determines all polynomial derivatives

Pinned mathlib's exact polynomial derivation chain rule
  Derivation.comp_aeval_eq
and RatFunc's embedding identity
  RatFunc.aeval_X_left_eq_algebraMap
show that for a K-derivation D on K(x), the SINGLE identity

    D (RatFunc.X) = 1

forces D to extend ordinary polynomial differentiation. There is
no need to assume a compatibility lemma for each polynomial separately.

Combining this with the coprime-numerator proof of the constant field
gives a rank-three Riccati-to-polynomial-inverse theorem requiring
only D(X)=1 and the genuine Riccati identity.

Construction of the derivation D on the rational function field is
the remaining differential-algebra setup task; it is not a
new geometric hypothesis.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A K-linear derivation on rational functions taking X to 1
necessarily restricts to the ORDINARY polynomial derivative. -/
theorem quadraticTransverse_ratFunc_derivation_polynomialCompatibility
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hX : D (RatFunc.X : RatFunc K) = 1) :
    ∀ p : Polynomial K,
      D ((algebraMap (Polynomial K) (RatFunc K)) p) =
        (algebraMap (Polynomial K) (RatFunc K))
          (Polynomial.derivative p) := by
  intro p
  have hchain := D.comp_aeval_eq (RatFunc.X : RatFunc K) p
  rw [hX] at hchain
  have hchain' :
      D (Polynomial.aeval (RatFunc.X : RatFunc K) p) =
        Polynomial.aeval (RatFunc.X : RatFunc K)
          (Polynomial.derivative p) := by
    simpa using hchain
  simpa only [RatFunc.aeval_X_left_eq_algebraMap] using hchain'

/-- The ground field is EXACTLY the constant field of any
K-derivation of K(x) satisfying D X=1. No separate constants
hypothesis or polynomial derivative compatibility is assumed. -/
theorem quadraticTransverse_ratFunc_constants_of_derivation_X
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hX : D (RatFunc.X : RatFunc K) = 1) :
    ∀ z : RatFunc K, D z = 0 →
      ∃ c : K,
        z = (algebraMap (Polynomial K) (RatFunc K))
          (Polynomial.C c) := by
  exact quadraticTransverse_ratFunc_derivation_constants D
    (quadraticTransverse_ratFunc_derivation_polynomialCompatibility D hX)

/-- **Generic rank-three algebra over K(x) with one derivation input.**

If a K-derivation D on K(x) satisfies D X=1, the matrix
Riccati identity forces a genuine POLYNOMIAL two-sided inverse
and a nonzero CONSTANT transverse determinant.

Only Riccati and D(X)=1 remain as differential input: polynomial
compatibility and the constants-field theorem are proved above. -/
theorem quadraticTransverse_ratFuncRiccati_polynomialInverse_of_derivation_X
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hX : D (RatFunc.X : RatFunc K) = 1)
    (C : Matrix (Fin 3) (Fin 3) (Polynomial K))
    (M : Matrix (Fin 3) (Fin 3) (RatFunc K))
    (hCM : C.map (algebraMap (Polynomial K) (RatFunc K)) * M = 1)
    (hMC : M * C.map (algebraMap (Polynomial K) (RatFunc K)) = 1)
    (hRiccati :
      quadraticTransverse_fieldMatrixDerivative D
          (quadraticTransverse_fieldMatrixDerivative D
            (C.map (algebraMap (Polynomial K) (RatFunc K)))) =
        2 * ((quadraticTransverse_fieldMatrixDerivative D
                (C.map (algebraMap (Polynomial K) (RatFunc K))) * M) *
          quadraticTransverse_fieldMatrixDerivative D
            (C.map (algebraMap (Polynomial K) (RatFunc K))))) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Polynomial K),
      C * P = 1 ∧ P * C = 1 ∧
        ∃ d : K, d ≠ 0 ∧ C.det = Polynomial.C d := by
  exact quadraticTransverse_ratFuncRiccati_polynomialInverse
    D (quadraticTransverse_ratFunc_derivation_polynomialCompatibility D hX)
    C M hCM hMC hRiccati

end

end HC4.Valuation
