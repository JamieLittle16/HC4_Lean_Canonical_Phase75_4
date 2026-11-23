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
      have hX : E (MvPolynomial.X j) = q j := by
        exact MvPolynomial.aeval_X q j
      have hpartialX (i : Fin 4) :
          E (MvPolynomial.pderiv i (MvPolynomial.X j)) =
            if i = j then (1 : Polynomial K) else 0 := by
        by_cases hij : i = j
        · subst i
          simp
        · have hji : j ≠ i := Ne.symm hij
          rw [MvPolynomial.pderiv_X_of_ne hji]
          simp [hij]
      have hpartial (i : Fin 4) :
          E (MvPolynomial.pderiv i (P * MvPolynomial.X j)) =
            E (MvPolynomial.pderiv i P) * q j +
              if i = j then E P else 0 := by
        rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
          hX, hpartialX]
        by_cases hij : i = j <;> simp [hij]
      have hsum :
          (∑ i : Fin 4, Polynomial.derivative (q i) *
              E (MvPolynomial.pderiv i (P * MvPolynomial.X j))) =
            (∑ i : Fin 4, Polynomial.derivative (q i) *
              E (MvPolynomial.pderiv i P)) * q j +
              E P * Polynomial.derivative (q j) := by
        calc
          (∑ i : Fin 4, Polynomial.derivative (q i) *
              E (MvPolynomial.pderiv i (P * MvPolynomial.X j))) =
              (∑ i : Fin 4,
                (Polynomial.derivative (q i) *
                  E (MvPolynomial.pderiv i P)) * q j) +
              (∑ i : Fin 4,
                if i = j then Polynomial.derivative (q j) * E P else 0) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro i _
                rw [hpartial i]
                by_cases hij : i = j
                · subst i
                  simp only [ite_true]
                  ring
                · simp only [if_neg hij, mul_add, mul_zero, add_zero]
                  ring
          _ = (∑ i : Fin 4, Polynomial.derivative (q i) *
                  E (MvPolynomial.pderiv i P)) * q j +
                E P * Polynomial.derivative (q j) := by
              rw [← Finset.sum_mul]
              simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
              ring
      calc
        Polynomial.derivative (E (P * MvPolynomial.X j)) =
            Polynomial.derivative (E P * q j) := by rw [map_mul, hX]
        _ = Polynomial.derivative (E P) * q j +
              E P * Polynomial.derivative (q j) := by
                rw [Polynomial.derivative_mul]
        _ = (∑ i : Fin 4, Polynomial.derivative (q i) *
              E (MvPolynomial.pderiv i P)) * q j +
              E P * Polynomial.derivative (q j) := by rw [ihP]
        _ = (∑ i : Fin 4, Polynomial.derivative (q i) *
              E (MvPolynomial.pderiv i (P * MvPolynomial.X j))) := hsum.symm

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
