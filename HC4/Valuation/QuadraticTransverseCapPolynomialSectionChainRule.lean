import HC4.Valuation.QuadraticTransverseCapSourceRegularFibre
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic

/-!
# Formal chain rule for polynomial curves through the actual source

Given a polynomial path `q : Fin 4 → Polynomial K`, substituting
its entries into any four-variable polynomial `F` and differentiating
with respect to the source parameter obeys the exact chain rule

  d(F(q(x)))/dx = ∑ᵢ qᵢ'(x) (∂ᵢF)(q(x)).

This is an identity in K[X], not an analytic or pointwise derivative.
It is the missing source-level mechanism for differentiating the
longitudinal gradient along the inverse transverse-gradient fibre.

No Hessian-rank, determinant or cap assumption is needed here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 2048

variable {K : Type*} [Field K]

/-- Multivariate polynomial substitution along a one-parameter
polynomial path, viewed as a true `K`-algebra homomorphism. -/
noncomputable def sourcePolynomialPathSubstitution
    (q : Fin 4 → Polynomial K) :
    MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval q

/-- Formal polynomial chain rule on four variables, valid
without assumptions on the potential or on the polynomial path. -/
theorem sourcePolynomialPath_derivative
    (F : MvPolynomial (Fin 4) K)
    (q : Fin 4 → Polynomial K) :
    Polynomial.derivative (sourcePolynomialPathSubstitution q F) =
      ∑ i : Fin 4, Polynomial.derivative (q i) *
        sourcePolynomialPathSubstitution q
          (MvPolynomial.pderiv i F) := by
  classical
  let E := sourcePolynomialPathSubstitution q
  change Polynomial.derivative (E F) =
    ∑ i : Fin 4, Polynomial.derivative (q i) *
      E (MvPolynomial.pderiv i F)
  induction F using MvPolynomial.induction_on with
  | C a =>
      simp [E, sourcePolynomialPathSubstitution]
  | add P Q ihP ihQ =>
      simp only [map_add, Polynomial.derivative_add,
        Finset.sum_add_distrib, mul_add]
      rw [ihP, ihQ]
  | mul_X P j ihP =>
      fin_cases j <;>
        simp [E, sourcePolynomialPathSubstitution,
          MvPolynomial.pderiv_mul, Polynomial.derivative_mul,
          Fin.sum_univ_four, ihP] <;>
        ring

/-- Chain rule specialized to a longitudinal coordinate X and
polynomial transverse-coordinate path `y(X)`.

Its longitudinal term has coefficient one; its other terms
are the transverse derivatives weighted by `yᵢ'(X)`. -/
theorem sourcePolynomialLongitudinalSection_derivative
    (F : MvPolynomial (Fin 4) K)
    (y : Fin 3 → Polynomial K) :
    Polynomial.derivative
        (sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y) F) =
      sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
        (MvPolynomial.pderiv (0 : Fin 4) F) +
      ∑ i : Fin 3, Polynomial.derivative (y i) *
        sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
          (MvPolynomial.pderiv i.succ F) := by
  have h := sourcePolynomialPath_derivative
    F (Fin.cons Polynomial.X y)
  simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Polynomial.derivative_X, one_mul] using h

end

end HC4.Valuation
