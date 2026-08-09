import HC4.Polynomial.RankThreePencils
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Complementary rank-two logarithmic Hessian certificate

This file formalises the exact algebraic calculation used in Section 5 of the
symmetric-gradings manuscript.  For complementary monomials

  U = x₁^α₁ x₂^α₂,   V = x₃^β₁ x₄^β₂,

and an edge written as `V^(kM) φ(U^h/V^k)`, the logarithmic Hessian has core

  e eᵀ + η w wᵀ - diag(e),

with

  e = (ρhα₁, ρhα₂, kβ₁(M-ρ), kβ₂(M-ρ)),
  w = (hα₁, hα₂, -kβ₁, -kβ₂).

The determinant is linear in η after the universal nonzero prefactor is
removed.  We also package the numerator and denominator of the resulting
rational η-equation as polynomials in ρ and kernel-check the endpoint
coefficient ratio `1/(A0*h)`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- Exponent vector `e = v + ρw` for the complementary-edge logarithmic
Hessian calculation. -/
def complementaryLogExponent {K : Type*} [CommRing K]
    (a1 a2 b1 b2 h k M rho : K) : Fin 4 → K :=
  ![rho * h * a1,
    rho * h * a2,
    k * b1 * (M - rho),
    k * b2 * (M - rho)]

/-- Direction vector `w` for the complementary edge. -/
def complementaryLogDirection {K : Type*} [CommRing K]
    (a1 a2 b1 b2 h k : K) : Fin 4 → K :=
  ![h * a1, h * a2, -(k * b1), -(k * b2)]

/-- The coefficient-valued logarithmic Hessian core
`e eᵀ + η w wᵀ - diag(e)`. -/
def complementaryLogHessianCore {K : Type*} [CommRing K]
    (a1 a2 b1 b2 h k M rho eta : K) : Matrix (Fin 4) (Fin 4) K :=
  let e := complementaryLogExponent a1 a2 b1 b2 h k M rho
  let w := complementaryLogDirection a1 a2 b1 b2 h k
  Matrix.of fun i j =>
    e i * e j + eta * (w i * w j) - if i = j then e i else 0

set_option maxHeartbeats 4000000

/-- Exact determinant identity for the complementary logarithmic Hessian.
This is the manuscript calculation preceding the rational equation for η. -/
theorem det_complementaryLogHessianCore
    {K : Type*} [CommRing K]
    (a1 a2 b1 b2 h k M rho eta : K) :
    (complementaryLogHessianCore a1 a2 b1 b2 h k M rho eta).det =
      a1 * a2 * b1 * b2 * h^2 * k^2 * rho * (M - rho) *
        (((a1 + a2) * (b1 + b2) * M^2 * h * k
            - (a1 + a2) * M * h
            + ((a1 + a2) * h - (b1 + b2) * k) * rho) * eta
          - rho * (M - rho) *
            ((b1 + b2) * M * k
              + ((a1 + a2) * h - (b1 + b2) * k) * rho - 1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [complementaryLogHessianCore, complementaryLogExponent,
    complementaryLogDirection, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Polynomial numerator of the complementary-edge rational equation for η. -/
def complementaryEtaNumerator {K : Type*} [CommRing K]
    (A0 B0 M h k : K) : Polynomial K :=
  Polynomial.X * (Polynomial.C M - Polynomial.X) *
    (Polynomial.C (B0 * M * k - 1) +
      Polynomial.C (A0 * h - B0 * k) * Polynomial.X)

/-- Polynomial denominator of the complementary-edge rational equation for η. -/
def complementaryEtaDenominator {K : Type*} [CommRing K]
    (A0 B0 M h k : K) : Polynomial K :=
  Polynomial.C (A0 * B0 * M^2 * h * k - A0 * M * h) +
    Polynomial.C (A0 * h - B0 * k) * Polynomial.X

/-- The numerator vanishes to first order at `ρ=0`, with the displayed
linear coefficient. -/
theorem coeff_one_complementaryEtaNumerator
    {K : Type*} [CommRing K]
    (A0 B0 M h k : K) :
    (complementaryEtaNumerator A0 B0 M h k).coeff 1 =
      M * (B0 * M * k - 1) := by
  have hcalc :
      Polynomial.eval 0
          (Polynomial.derivative (complementaryEtaNumerator A0 B0 M h k)) =
        M * (B0 * M * k - 1) := by
    simp [complementaryEtaNumerator, Polynomial.derivative_mul]
  rw [← Polynomial.coeff_zero_eq_eval_zero] at hcalc
  simpa [Polynomial.coeff_derivative] using hcalc

/-- The denominator's constant term factors as in the manuscript. -/
theorem coeff_zero_complementaryEtaDenominator
    {K : Type*} [CommRing K]
    (A0 B0 M h k : K) :
    (complementaryEtaDenominator A0 B0 M h k).coeff 0 =
      A0 * M * h * (B0 * M * k - 1) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [complementaryEtaDenominator]
  ring

/-- Algebraic version of the manuscript's endpoint slope computation:
provided the factors that are cancelled there are nonzero, the ratio of the
first numerator coefficient to the denominator constant coefficient is
`1/(A0*h)`. -/
theorem complementaryEta_initial_ratio
    {K : Type*} [Field K]
    {A0 B0 M h k : K}
    (hA0 : A0 ≠ 0) (hM : M ≠ 0) (hh : h ≠ 0)
    (hres : B0 * M * k - 1 ≠ 0) :
    (complementaryEtaNumerator A0 B0 M h k).coeff 1 /
        (complementaryEtaDenominator A0 B0 M h k).coeff 0 =
      1 / (A0 * h) := by
  rw [coeff_one_complementaryEtaNumerator,
    coeff_zero_complementaryEtaDenominator]
  have hAh : A0 * h ≠ 0 := mul_ne_zero hA0 hh
  have hden : A0 * M * h * (B0 * M * k - 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hA0 hM) hh) hres
  apply (div_eq_iff hden).2
  field_simp [hAh] <;> ring

end

end HC4.Polynomial
