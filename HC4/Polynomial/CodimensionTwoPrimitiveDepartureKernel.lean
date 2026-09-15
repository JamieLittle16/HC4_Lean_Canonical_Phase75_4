import HC4.Polynomial.CodimensionTwoPrimitiveDepartureClassification
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Constant kernels of the classified codimension-two departure forms

The exponent classification from
`CodimensionTwoPrimitiveDepartureClassification` has a particularly simple
polynomial endpoint: no explicit source shear is needed.  Each surviving
trinomial already has a literal constant directional derivative.

For the three paper cases:

* two primitive departures with the same active exponent are killed by
  `B ∂₂ - A ∂₃`;
* the lower asymmetric endpoint is killed by `A ∂₀ - C ∂₂`;
* the upper asymmetric endpoint is killed by `A ∂₁ - C ∂₂`.

Thus each classified local carrier has a constant Hessian-kernel direction as
soon as its displayed endpoint coefficients are nonzero.  This file is
state-free and introduces no repair transition.
-/

namespace HC4.Polynomial

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Two primitive departures with common active exponent `a`. -/
noncomputable def codimensionTwoPrimitivePairForm
    (D p a : ℕ) (C A B : K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.C C * X 0 ^ p * X 1 ^ (D - p) +
    MvPolynomial.C A * X 0 ^ a * X 1 ^ (D - 1 - a) * X 2 +
    MvPolynomial.C B * X 0 ^ a * X 1 ^ (D - 1 - a) * X 3

/-- The common-active-exponent form has the literal kernel direction
`B ∂₂ - A ∂₃`. -/
theorem codimensionTwoPrimitivePair_directionalDerivative_zero
    (D p a : ℕ) (C A B : K) :
    MvPolynomial.C B *
        MvPolynomial.pderiv (2 : Fin 4)
          (codimensionTwoPrimitivePairForm D p a C A B) -
      MvPolynomial.C A *
        MvPolynomial.pderiv (3 : Fin 4)
          (codimensionTwoPrimitivePairForm D p a C A B) = 0 := by
  simp [codimensionTwoPrimitivePairForm]
  ring

/-- Lower asymmetric endpoint `(a,p,c)=(0,1,0)`. -/
noncomputable def codimensionTwoLowerEndpointForm
    (D n : ℕ) (C A B : K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.C C * X 0 * X 1 ^ (D - 1) +
    MvPolynomial.C A * X 1 ^ (D - 1) * X 2 +
    MvPolynomial.C B * X 1 ^ (D - n) * X 3 ^ n

/-- The lower asymmetric endpoint has literal kernel `A ∂₀ - C ∂₂`. -/
theorem codimensionTwoLowerEndpoint_directionalDerivative_zero
    (D n : ℕ) (C A B : K) :
    MvPolynomial.C A *
        MvPolynomial.pderiv (0 : Fin 4)
          (codimensionTwoLowerEndpointForm D n C A B) -
      MvPolynomial.C C *
        MvPolynomial.pderiv (2 : Fin 4)
          (codimensionTwoLowerEndpointForm D n C A B) = 0 := by
  simp [codimensionTwoLowerEndpointForm]
  ring

/-- Upper asymmetric endpoint `(a,p,c)=(D-1,D-1,D-n)`. -/
noncomputable def codimensionTwoUpperEndpointForm
    (D n : ℕ) (C A B : K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.C C * X 0 ^ (D - 1) * X 1 +
    MvPolynomial.C A * X 0 ^ (D - 1) * X 2 +
    MvPolynomial.C B * X 0 ^ (D - n) * X 3 ^ n

/-- The upper asymmetric endpoint has literal kernel `A ∂₁ - C ∂₂`. -/
theorem codimensionTwoUpperEndpoint_directionalDerivative_zero
    (D n : ℕ) (C A B : K) :
    MvPolynomial.C A *
        MvPolynomial.pderiv (1 : Fin 4)
          (codimensionTwoUpperEndpointForm D n C A B) -
      MvPolynomial.C C *
        MvPolynomial.pderiv (2 : Fin 4)
          (codimensionTwoUpperEndpointForm D n C A B) = 0 := by
  simp [codimensionTwoUpperEndpointForm]
  ring

end

end HC4.Polynomial
