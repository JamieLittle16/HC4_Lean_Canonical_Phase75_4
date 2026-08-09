import HC4.Polynomial.RankThreeLinearCoefficient
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Tactic

/-!
# Algebraic reconstruction for the autonomous logarithmic ODE

This file formalises the final reconstruction step of the autonomous
logarithmic-ODE lemma used in the symmetric-gradings rank-three edge proof.

After the projective/rational rigidity part of that lemma has identified

    rho(t) = m M lambda t^m / (1 + lambda t^m),

with `rho = t phi' / phi`, clearing denominators gives the polynomial ODE

    (X phi') (1 + lambda X^m) = m M lambda X^m phi.

Rather than introducing analytic integration, we prove algebraically that this
first-order equation has a unique polynomial solution with prescribed constant
coefficient, namely

    phi = c (1 + lambda X^m)^M.

The uniqueness proof uses the lowest nonzero coefficient of the difference of
two solutions.  This is exactly the reconstruction needed after the rational
part of manuscript Lemma 4.1.
-/

namespace HC4.Polynomial

noncomputable section

/-- Euler's differential operator `X d/dX` on a polynomial. -/
def eulerDerivative {K : Type*} [Semiring K]
    (p : Polynomial K) : Polynomial K :=
  Polynomial.X * Polynomial.derivative p

/-- Coefficient formula for the Euler derivative. -/
theorem coeff_eulerDerivative {K : Type*} [CommSemiring K]
    (p : Polynomial K) (n : ℕ) :
    (eulerDerivative p).coeff n = (n : K) * p.coeff n := by
  cases n with
  | zero =>
      simp [eulerDerivative]
  | succ n =>
      simp [eulerDerivative, Polynomial.coeff_derivative]
      ring

/-- The denominator-cleared first-order ODE obtained from the logistic form of
`rho = X phi' / phi`. -/
def SeparatedBinomialODE {K : Type*} [CommRing K]
    (m M : ℕ) (lam : K) (p : Polynomial K) : Prop :=
  eulerDerivative p *
      (1 + Polynomial.C lam * Polynomial.X ^ m) =
    Polynomial.C (((m * M : ℕ) : K) * lam) *
      Polynomial.X ^ m * p

/-- Expanded form of `SeparatedBinomialODE`, convenient for coefficient
arguments. -/
theorem separatedBinomialODE_iff_expanded
    {K : Type*} [CommRing K]
    (m M : ℕ) (lam : K) (p : Polynomial K) :
    SeparatedBinomialODE m M lam p ↔
      eulerDerivative p +
          (Polynomial.C lam * Polynomial.X ^ m) * eulerDerivative p =
        Polynomial.C (((m * M : ℕ) : K) * lam) *
          Polynomial.X ^ m * p := by
  unfold SeparatedBinomialODE
  constructor <;> intro h
  · calc
      eulerDerivative p +
          (Polynomial.C lam * Polynomial.X ^ m) * eulerDerivative p =
          eulerDerivative p *
            (1 + Polynomial.C lam * Polynomial.X ^ m) := by ring
      _ = Polynomial.C (((m * M : ℕ) : K) * lam) *
            Polynomial.X ^ m * p := h
  · calc
      eulerDerivative p *
          (1 + Polynomial.C lam * Polynomial.X ^ m) =
          eulerDerivative p +
            (Polynomial.C lam * Polynomial.X ^ m) * eulerDerivative p := by ring
      _ = Polynomial.C (((m * M : ℕ) : K) * lam) *
            Polynomial.X ^ m * p := h

/-- Euler differentiation is additive over subtraction. -/
theorem eulerDerivative_sub {K : Type*} [CommRing K]
    (p q : Polynomial K) :
    eulerDerivative (p - q) = eulerDerivative p - eulerDerivative q := by
  simp [eulerDerivative, Polynomial.derivative_sub]
  ring

/-- The separated ODE is linear in the unknown polynomial. -/
theorem SeparatedBinomialODE.sub
    {K : Type*} [CommRing K]
    {m M : ℕ} {lam : K} {p q : Polynomial K}
    (hp : SeparatedBinomialODE m M lam p)
    (hq : SeparatedBinomialODE m M lam q) :
    SeparatedBinomialODE m M lam (p - q) := by
  rw [separatedBinomialODE_iff_expanded]
  have hp' := (separatedBinomialODE_iff_expanded m M lam p).1 hp
  have hq' := (separatedBinomialODE_iff_expanded m M lam q).1 hq
  rw [eulerDerivative_sub]
  linear_combination hp' - hq'

/-- A zero-constant polynomial solution of the separated ODE is zero.

The proof looks at the least exponent `n` with nonzero coefficient.  Because
`m > 0`, every shifted term in the ODE at degree `n` comes from a strictly
smaller coefficient and therefore vanishes.  What remains is
`n * coeff n = 0`, contradicting characteristic zero. -/
theorem eq_zero_of_separatedBinomialODE_of_coeff_zero
    {K : Type*} [Field K] [CharZero K]
    {m M : ℕ} {lam : K} {p : Polynomial K}
    (hm : 0 < m)
    (hp0 : p.coeff 0 = 0)
    (hode : SeparatedBinomialODE m M lam p) :
    p = 0 := by
  by_contra hp
  let n := p.natTrailingDegree
  have hn0 : n ≠ 0 := by
    exact (Polynomial.natTrailingDegree_ne_zero).2 ⟨hp, hp0⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hcn : p.coeff n ≠ 0 := by
    exact (Polynomial.coeff_natTrailingDegree_ne_zero).2 hp

  have hexpanded :=
    (separatedBinomialODE_iff_expanded m M lam p).1 hode

  have hshiftEulerZero :
      ((Polynomial.C lam * Polynomial.X ^ m) * eulerDerivative p).coeff n = 0 := by
    rw [show
      (Polynomial.C lam * Polynomial.X ^ m) * eulerDerivative p =
        Polynomial.C lam * (Polynomial.X ^ m * eulerDerivative p) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    by_cases hmn : m ≤ n
    · have hlt : n - m < n := by omega
      have hbelow : p.coeff (n - m) = 0 :=
        Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt
      simp [hmn, coeff_eulerDerivative, hbelow]
    · simp [hmn]

  have hshiftPZero :
      (Polynomial.C (((m * M : ℕ) : K) * lam) *
          Polynomial.X ^ m * p).coeff n = 0 := by
    rw [show
      Polynomial.C (((m * M : ℕ) : K) * lam) *
          Polynomial.X ^ m * p =
        Polynomial.C (((m * M : ℕ) : K) * lam) *
          (Polynomial.X ^ m * p) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    by_cases hmn : m ≤ n
    · have hlt : n - m < n := by omega
      have hbelow : p.coeff (n - m) = 0 :=
        Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt
      simp [hmn, hbelow]
    · simp [hmn]

  have hcoeff :
      (eulerDerivative p).coeff n +
          ((Polynomial.C lam * Polynomial.X ^ m) * eulerDerivative p).coeff n =
        (Polynomial.C (((m * M : ℕ) : K) * lam) *
          Polynomial.X ^ m * p).coeff n := by
    simpa only [Polynomial.coeff_add] using
      congrArg (fun q : Polynomial K => q.coeff n) hexpanded
  rw [coeff_eulerDerivative, hshiftEulerZero, hshiftPZero] at hcoeff
  have hmain : (n : K) * p.coeff n = 0 := by
    simpa using hcoeff

  have hnK : (n : K) ≠ 0 := by
    exact_mod_cast hn0
  have : p.coeff n = 0 :=
    (mul_eq_zero.mp hmain).resolve_left hnK
  exact hcn this

/-- The candidate binomial polynomial reconstructed from the autonomous ODE. -/
def binomialODEModel {K : Type*} [CommRing K]
    (c lam : K) (m M : ℕ) : Polynomial K :=
  Polynomial.C c *
    (1 + Polynomial.C lam * Polynomial.X ^ m) ^ M

/-- The binomial model has the prescribed constant coefficient when `m > 0`. -/
theorem coeff_zero_binomialODEModel
    {K : Type*} [CommRing K]
    (c lam : K) {m M : ℕ} (hm : 0 < m) :
    (binomialODEModel c lam m M).coeff 0 = c := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [binomialODEModel, Nat.ne_of_gt hm]

/-- The binomial model satisfies the denominator-cleared separated ODE. -/
theorem binomialODEModel_satisfies
    {K : Type*} [CommRing K]
    (c lam : K) {m M : ℕ} (hm : 0 < m) :
    SeparatedBinomialODE m M lam
      (binomialODEModel c lam m M) := by
  rcases m with _ | m
  · omega
  rcases M with _ | M
  · simp [SeparatedBinomialODE, binomialODEModel, eulerDerivative]
  · simp [SeparatedBinomialODE, binomialODEModel, eulerDerivative,
      Polynomial.derivative_mul, Polynomial.derivative_pow_succ,
      Polynomial.derivative_X_pow_succ]
    ring

/-- Algebraic replacement for the manuscript's final "separate and integrate"
step: a polynomial satisfying the separated first-order equation is uniquely
the binomial model once its constant coefficient is fixed. -/
theorem eq_binomialODEModel_of_separatedBinomialODE
    {K : Type*} [Field K] [CharZero K]
    {m M : ℕ} {lam c : K} {p : Polynomial K}
    (hm : 0 < m)
    (hp0 : p.coeff 0 = c)
    (hode : SeparatedBinomialODE m M lam p) :
    p = binomialODEModel c lam m M := by
  have hmodel :
      SeparatedBinomialODE m M lam
        (binomialODEModel c lam m M) :=
    binomialODEModel_satisfies c lam hm
  have hsub :
      SeparatedBinomialODE m M lam
        (p - binomialODEModel c lam m M) :=
    hode.sub hmodel
  have hsub0 :
      (p - binomialODEModel c lam m M).coeff 0 = 0 := by
    rw [Polynomial.coeff_sub, hp0,
      coeff_zero_binomialODEModel c lam hm]
    ring
  have hz :=
    eq_zero_of_separatedBinomialODE_of_coeff_zero
      (m := m) (M := M) (lam := lam)
      hm hsub0 hsub
  exact sub_eq_zero.mp hz

end

end HC4.Polynomial
