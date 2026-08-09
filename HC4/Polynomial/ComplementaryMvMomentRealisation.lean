import HC4.Polynomial.ComplementaryMvSubstitution
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Realising the complementary moment Hessian from the actual MvPolynomial

This is the final algebraic bridge between the honest complementary line
polynomial from Phase 73 and the line-moment logarithmic Hessian from Phase 72.

Phase 74.1 deliberately works monomial-first.  Each honest line term is first
identified with one `MvPolynomial.monomial`; Mathlib's theorem
`MvPolynomial.X_mul_pderiv_monomial` then gives the Euler action without any
case split on zero exponents or subtraction of powers.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- The actual nonnegative exponent vector of the `j`th term of the honest
complementary line polynomial, with values cast into the coefficient field. -/
def complementaryLineExponentValue
    {K : Type*} [NatCast K]
    (a1 a2 b1 b2 h k M j : ℕ) : Fin 4 → K :=
  ![((h * a1 * j : ℕ) : K),
    ((h * a2 * j : ℕ) : K),
    ((k * b1 * (M - j) : ℕ) : K),
    ((k * b2 * (M - j) : ℕ) : K)]

/-- The same exponent vector as an actual finitely-supported exponent. -/
def complementaryLineExponentFinsupp
    (a1 a2 b1 b2 h k M j : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (0 : Fin 4) (h * a1 * j) +
    Finsupp.single (1 : Fin 4) (h * a2 * j) +
    Finsupp.single (2 : Fin 4) (k * b1 * (M - j)) +
    Finsupp.single (3 : Fin 4) (k * b2 * (M - j))

@[simp] theorem complementaryLineExponentFinsupp_apply
    (a1 a2 b1 b2 h k M j : ℕ) (i : Fin 4) :
    complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j i =
      ![h * a1 * j, h * a2 * j,
        k * b1 * (M - j), k * b2 * (M - j)] i := by
  fin_cases i <;>
    simp [complementaryLineExponentFinsupp]

/-- Casting the finitely-supported exponent gives the coefficient-field vector
used in the moment calculations. -/
theorem complementaryLineExponentFinsupp_cast
    {K : Type*} [Field K] [CharZero K]
    (a1 a2 b1 b2 h k M j : ℕ) (i : Fin 4) :
    ((complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j i : ℕ) : K) =
      complementaryLineExponentValue (K := K) a1 a2 b1 b2 h k M j i := by
  fin_cases i <;>
    simp [complementaryLineExponentFinsupp, complementaryLineExponentValue]

/-- The honest product presentation from Phase 73 is a single multivariate
monomial. -/
theorem complementaryLineTerm_eq_monomial
    {K : Type*} [Field K]
    (a1 a2 b1 b2 h k M j : ℕ) (c : K) :
    complementaryLineTerm a1 a2 b1 b2 h k M j c =
      MvPolynomial.monomial
        (complementaryLineExponentFinsupp a1 a2 b1 b2 h k M j) c := by
  simp only [complementaryLineTerm, MvPolynomial.X_pow_eq_monomial]
  rw [MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  simp only [mul_one]
  apply congrArg (fun d => MvPolynomial.monomial d c)
  ext i
  fin_cases i <;>
    simp [complementaryLineExponentFinsupp, mul_assoc, add_assoc]

/-- On the actual support (`j ≤ M`), the nonnegative exponent vector is the
affine line `v + j w` used by the logarithmic-Hessian moments. -/
theorem complementaryLineExponentValue_eq_affine
    {K : Type*} [Field K] [CharZero K]
    (a1 a2 b1 b2 h k M j : ℕ) (hj : j ≤ M) :
    complementaryLineExponentValue (K := K) a1 a2 b1 b2 h k M j =
      fun i =>
        complementaryLogBaseExponent (b1 : K) (b2 : K) (k : K) (M : K) i +
          (j : K) *
            complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i := by
  funext i
  fin_cases i
  · simp [complementaryLineExponentValue, complementaryLogBaseExponent,
      complementaryLogDirection]
    ring
  · simp [complementaryLineExponentValue, complementaryLogBaseExponent,
      complementaryLogDirection]
    ring
  · simp [complementaryLineExponentValue, complementaryLogBaseExponent,
      complementaryLogDirection, Nat.cast_sub hj]
    ring
  · simp [complementaryLineExponentValue, complementaryLogBaseExponent,
      complementaryLogDirection, Nat.cast_sub hj]
    ring

/-- Euler differentiation of a single honest complementary line term simply
multiplies it by the corresponding exponent. -/
theorem mvEuler_complementaryLineTerm
    {K : Type*} [Field K] [CharZero K]
    (a1 a2 b1 b2 h k M j : ℕ) (c : K) (i : Fin 4) :
    mvEuler i (complementaryLineTerm a1 a2 b1 b2 h k M j c) =
      MvPolynomial.C
          (complementaryLineExponentValue (K := K)
            a1 a2 b1 b2 h k M j i) *
        complementaryLineTerm a1 a2 b1 b2 h k M j c := by
  rw [complementaryLineTerm_eq_monomial]
  unfold mvEuler
  rw [MvPolynomial.X_mul_pderiv_monomial]
  rw [← complementaryLineTerm_eq_monomial]
  rw [← complementaryLineExponentFinsupp_cast (K := K)]
  simp [nsmul_eq_mul]

/-- Euler multiplication commutes with a coefficient constant. -/
theorem mvEuler_C_mul
    {K : Type*} [Field K]
    (i : Fin 4) (a : K) (p : MvPolynomial (Fin 4) K) :
    mvEuler i (MvPolynomial.C a * p) = MvPolynomial.C a * mvEuler i p := by
  simp [mvEuler, MvPolynomial.pderiv_C_mul]
  ring

/-- The Euler-scaled Hessian of one line term has the expected exponent-core
coefficient before specialisation. -/
theorem eulerScaledHessian_complementaryLineTerm
    {K : Type*} [Field K] [CharZero K]
    (a1 a2 b1 b2 h k M j : ℕ) (c : K) (i l : Fin 4) :
    eulerScaledHessian
        (complementaryLineTerm a1 a2 b1 b2 h k M j c) i l =
      MvPolynomial.C
          (complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j i *
            complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j l -
            if i = l then
              complementaryLineExponentValue (K := K)
                a1 a2 b1 b2 h k M j i
            else 0) *
        complementaryLineTerm a1 a2 b1 b2 h k M j c := by
  change
    mvEuler i (mvEuler l (complementaryLineTerm a1 a2 b1 b2 h k M j c)) -
        (if i = l then mvEuler i (complementaryLineTerm a1 a2 b1 b2 h k M j c) else 0) = _
  rw [mvEuler_complementaryLineTerm (K := K) a1 a2 b1 b2 h k M j c l]
  rw [mvEuler_C_mul]
  rw [mvEuler_complementaryLineTerm (K := K) a1 a2 b1 b2 h k M j c i]
  by_cases hil : i = l
  · subst l
    simp [MvPolynomial.C_mul, MvPolynomial.C_sub]
    ring
  · simp [hil, MvPolynomial.C_mul]
    ring

/-- Specialised one-term Euler-Hessian formula. -/
theorem complementaryLineSpecialisation_eulerScaledHessian_term
    {K : Type*} [Field K] [CharZero K]
    (a1 a2 b1 b2 h k M j : ℕ) (c : K) (i l : Fin 4) :
    complementaryLineSpecialisation
        (eulerScaledHessian
          (complementaryLineTerm a1 a2 b1 b2 h k M j c) i l) =
      Polynomial.C
          (complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j i *
            complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j l -
            if i = l then
              complementaryLineExponentValue (K := K)
                a1 a2 b1 b2 h k M j i
            else 0) *
        (Polynomial.C c * Polynomial.X ^ (h * a1 * j)) := by
  rw [eulerScaledHessian_complementaryLineTerm]
  rw [map_mul]
  rw [complementaryLineSpecialisation_term]
  have hC :
      complementaryLineSpecialisation
        (MvPolynomial.C
          (complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j i *
            complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j l -
            if i = l then
              complementaryLineExponentValue (K := K)
                a1 a2 b1 b2 h k M j i
            else 0)) =
        Polynomial.C
          (complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j i *
            complementaryLineExponentValue (K := K)
              a1 a2 b1 b2 h k M j l -
            if i = l then
              complementaryLineExponentValue (K := K)
                a1 a2 b1 b2 h k M j i
            else 0) := by
    simp [complementaryLineSpecialisation]
  rw [hC]

/-- Euler differentiation is additive over a finite sum. -/
theorem mvEuler_sum
    {K : Type*} [Field K]
    {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 4) K)
    (i : Fin 4) :
    mvEuler i (∑ x ∈ s, f x) = ∑ x ∈ s, mvEuler i (f x) := by
  simp [mvEuler, map_sum, Finset.mul_sum]

/-- The Euler-scaled Hessian is additive in its polynomial argument. -/
theorem eulerScaledHessian_sum
    {K : Type*} [Field K]
    {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 4) K)
    (i l : Fin 4) :
    eulerScaledHessian (∑ x ∈ s, f x) i l =
      ∑ x ∈ s, eulerScaledHessian (f x) i l := by
  change
    mvEuler i (mvEuler l (∑ x ∈ s, f x)) -
        (if i = l then mvEuler i (∑ x ∈ s, f x) else 0) =
      ∑ x ∈ s, (mvEuler i (mvEuler l (f x)) - if i = l then mvEuler i (f x) else 0)
  rw [mvEuler_sum (s := s) (f := f) l]
  rw [mvEuler_sum (s := s) (f := fun x => mvEuler l (f x)) i]
  by_cases hil : i = l
  · subst l
    rw [mvEuler_sum (s := s) (f := f) i]
    simp only [if_pos]
    rw [← Finset.sum_sub_distrib]
  · simp [hil]

/-- A support exponent of a polynomial lies below every upper bound on its
natural degree. -/
theorem support_le_of_natDegree_le
    {K : Type*} [Field K]
    {phi : Polynomial K} {M j : ℕ}
    (hdeg : phi.natDegree ≤ M) (hj : j ∈ phi.support) :
    j ≤ M := by
  exact le_trans (Polynomial.le_natDegree_of_mem_supp j hj) hdeg

/-- The polynomial-valued line-moment matrix attached to `phi`. -/
def complementaryPolynomialMomentHessian
    {K : Type*} [Field K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  lineMomentHessian
    (fun i => Polynomial.C
      (complementaryLogBaseExponent
        (b1 : K) (b2 : K) (k : K) (M : K) i))
    (fun i => Polynomial.C
      (complementaryLogDirection
        (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i))
    phi (eulerDerivative phi) (eulerDerivative (eulerDerivative phi))

/-- Entrywise normal form of the polynomial-valued moment Hessian.  Constants
are collected on the right so coefficient extraction is immediate. -/
theorem complementaryPolynomialMomentHessian_apply
    {K : Type*} [Field K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K)
    (i l : Fin 4) :
    complementaryPolynomialMomentHessian a1 a2 b1 b2 h k M phi i l =
      phi * Polynomial.C
        (complementaryLogBaseExponent (b1 : K) (b2 : K) (k : K) (M : K) i *
            complementaryLogBaseExponent (b1 : K) (b2 : K) (k : K) (M : K) l -
          if i = l then
            complementaryLogBaseExponent (b1 : K) (b2 : K) (k : K) (M : K) i
          else 0) +
      eulerDerivative phi * Polynomial.C
        (complementaryLogBaseExponent (b1 : K) (b2 : K) (k : K) (M : K) i *
            complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) l +
          complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i *
            complementaryLogBaseExponent (b1 : K) (b2 : K) (k : K) (M : K) l -
          if i = l then
            complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i
          else 0) +
      eulerDerivative (eulerDerivative phi) * Polynomial.C
        (complementaryLogDirection
            (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i *
          complementaryLogDirection
            (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) l) := by
  by_cases hil : i = l
  · subst l
    simp [complementaryPolynomialMomentHessian, lineMomentHessian]
  · simp [complementaryPolynomialMomentHessian, lineMomentHessian, hil]

/-- Coefficient formula for the polynomial-valued line-moment matrix. -/
theorem coeff_complementaryPolynomialMomentHessian
    {K : Type*} [Field K] [CharZero K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K)
    (i l : Fin 4) (j : ℕ) :
    (complementaryPolynomialMomentHessian
        a1 a2 b1 b2 h k M phi i l).coeff j =
      phi.coeff j *
        ((complementaryLogBaseExponent
              (b1 : K) (b2 : K) (k : K) (M : K) i +
            (j : K) * complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i) *
          (complementaryLogBaseExponent
              (b1 : K) (b2 : K) (k : K) (M : K) l +
            (j : K) * complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) l) -
          if i = l then
            complementaryLogBaseExponent
                (b1 : K) (b2 : K) (k : K) (M : K) i +
              (j : K) * complementaryLogDirection
                (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i
          else 0) := by
  rw [complementaryPolynomialMomentHessian_apply]
  simp only [Polynomial.coeff_add, Polynomial.coeff_mul_C, coeff_eulerDerivative]
  by_cases hil : i = l <;> simp [hil] <;> ring

/-- A raw support-sum version of one moment-matrix entry.  It uses exactly the
same support as `phi`, which makes the substitution bridge transparent. -/
def complementaryRawMomentEntry
    {K : Type*} [Field K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K)
    (i l : Fin 4) : Polynomial K :=
  phi.sum fun j c =>
    Polynomial.C
      (c *
        ((complementaryLogBaseExponent
              (b1 : K) (b2 : K) (k : K) (M : K) i +
            (j : K) * complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i) *
          (complementaryLogBaseExponent
              (b1 : K) (b2 : K) (k : K) (M : K) l +
            (j : K) * complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) l) -
          if i = l then
            complementaryLogBaseExponent
                (b1 : K) (b2 : K) (k : K) (M : K) i +
              (j : K) * complementaryLogDirection
                (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i
          else 0)) * Polynomial.X ^ j

/-- Coefficients of the raw support-sum moment entry. -/
theorem coeff_complementaryRawMomentEntry
    {K : Type*} [Field K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K)
    (i l : Fin 4) (r : ℕ) :
    (complementaryRawMomentEntry a1 a2 b1 b2 h k M phi i l).coeff r =
      phi.coeff r *
        ((complementaryLogBaseExponent
              (b1 : K) (b2 : K) (k : K) (M : K) i +
            (r : K) * complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i) *
          (complementaryLogBaseExponent
              (b1 : K) (b2 : K) (k : K) (M : K) l +
            (r : K) * complementaryLogDirection
              (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) l) -
          if i = l then
            complementaryLogBaseExponent
                (b1 : K) (b2 : K) (k : K) (M : K) i +
              (r : K) * complementaryLogDirection
                (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i
          else 0) := by
  classical
  unfold complementaryRawMomentEntry
  rw [Polynomial.sum_def, Polynomial.finset_sum_coeff]
  by_cases hr : r ∈ phi.support
  · rw [Finset.sum_eq_single r]
    · simp only [Polynomial.coeff_C_mul_X_pow, if_pos]
    · intro b hb hbr
      have hrb : r ≠ b := Ne.symm hbr
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp [hrb]
    · intro hnot
      exact (hnot hr).elim
  · have hcoeff : phi.coeff r = 0 := by
      simpa [Polynomial.mem_support_iff] using hr
    have hsum :
        (∑ n ∈ phi.support,
          (Polynomial.C
            (phi.coeff n *
              ((complementaryLogBaseExponent
                    (b1 : K) (b2 : K) (k : K) (M : K) i +
                  (n : K) * complementaryLogDirection
                    (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i) *
                (complementaryLogBaseExponent
                    (b1 : K) (b2 : K) (k : K) (M : K) l +
                  (n : K) * complementaryLogDirection
                    (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) l) -
                if i = l then
                  complementaryLogBaseExponent
                      (b1 : K) (b2 : K) (k : K) (M : K) i +
                    (n : K) * complementaryLogDirection
                      (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i
                else 0)) * Polynomial.X ^ n).coeff r) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hrb : r ≠ b := by
        intro h
        apply hr
        simpa [h] using hb
      simp only [Polynomial.coeff_C_mul_X_pow]
      simp [hrb]
    rw [hsum, hcoeff]
    simp

/-- The raw support-sum entry is exactly the Euler-moment entry. -/
theorem complementaryRawMomentEntry_eq_moment
    {K : Type*} [Field K] [CharZero K]
    (a1 a2 b1 b2 h k M : ℕ) (phi : Polynomial K)
    (i l : Fin 4) :
    complementaryRawMomentEntry a1 a2 b1 b2 h k M phi i l =
      complementaryPolynomialMomentHessian a1 a2 b1 b2 h k M phi i l := by
  apply Polynomial.ext
  intro r
  rw [coeff_complementaryRawMomentEntry,
    coeff_complementaryPolynomialMomentHessian]

/-- Ring homomorphisms transport line-moment Hessians entrywise. -/
theorem mapMatrix_lineMomentHessian
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v w : Fin 4 → R) (S0 S1 S2 : R) :
    f.mapMatrix (lineMomentHessian v w S0 S1 S2) =
      lineMomentHessian (fun i => f (v i)) (fun i => f (w i))
        (f S0) (f S1) (f S2) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [lineMomentHessian]
  · simp [lineMomentHessian, hij]

/-- Raw form of the central specialisation theorem. -/
theorem complementaryLineSpecialisation_eulerScaledHessian_raw
    {K : Type*} [Field K] [CharZero K]
    {a1 a2 b1 b2 h k M : ℕ} {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    (complementaryLineSpecialisation.mapMatrix
      (eulerScaledHessian
        (complementaryLinePolynomial a1 a2 b1 b2 h k M phi))) =
      (Polynomial.X ^ (h * a1)).compRingHom.mapMatrix
        (Matrix.of fun i l =>
          complementaryRawMomentEntry a1 a2 b1 b2 h k M phi i l) := by
  apply Matrix.ext
  intro i l
  change
    complementaryLineSpecialisation
        (eulerScaledHessian
          (complementaryLinePolynomial a1 a2 b1 b2 h k M phi) i l) =
      (Polynomial.X ^ (h * a1)).compRingHom
        (complementaryRawMomentEntry a1 a2 b1 b2 h k M phi i l)
  simp only [complementaryLinePolynomial, Polynomial.sum_def]
  rw [eulerScaledHessian_sum]
  rw [map_sum]
  unfold complementaryRawMomentEntry
  simp only [Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjM : j ≤ M := support_le_of_natDegree_le hdeg hj
  rw [complementaryLineSpecialisation_eulerScaledHessian_term]
  have he := complementaryLineExponentValue_eq_affine
    (K := K) a1 a2 b1 b2 h k M j hjM
  have hei := congrFun he i
  have hel := congrFun he l
  rw [hei, hel]
  simp [Polynomial.coe_compRingHom_apply, pow_mul]
  by_cases hil : i = l <;> simp [hil]
  <;> ring

/-- The central Phase-74 bridge: after the substitution
`x₁=X, x₂=x₃=x₄=1`, the Euler-scaled Hessian of the honest line polynomial is
exactly the line-moment Hessian followed by `X ↦ X^(h*a₁)`. -/
theorem complementaryLineSpecialisation_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    {a1 a2 b1 b2 h k M : ℕ} {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    (complementaryLineSpecialisation.mapMatrix
      (eulerScaledHessian
        (complementaryLinePolynomial a1 a2 b1 b2 h k M phi))) =
      (Polynomial.X ^ (h * a1)).compRingHom.mapMatrix
        (complementaryPolynomialMomentHessian
          a1 a2 b1 b2 h k M phi) := by
  rw [complementaryLineSpecialisation_eulerScaledHessian_raw hdeg]
  apply congrArg ((Polynomial.X ^ (h * a1)).compRingHom.mapMatrix)
  apply Matrix.ext
  intro i l
  exact complementaryRawMomentEntry_eq_moment a1 a2 b1 b2 h k M phi i l

/-- Determinant form of the central realisation theorem. -/
theorem complementaryLineSpecialisation_det_eulerScaledHessian
    {K : Type*} [Field K] [CharZero K]
    {a1 a2 b1 b2 h k M : ℕ} {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    complementaryLineSpecialisation
        ((eulerScaledHessian
          (complementaryLinePolynomial a1 a2 b1 b2 h k M phi)).det) =
      ((complementaryPolynomialMomentHessian
          a1 a2 b1 b2 h k M phi).det).comp
        (Polynomial.X ^ (h * a1)) := by
  let s : MvPolynomial (Fin 4) K →+* Polynomial K :=
    complementaryLineSpecialisation
  let c : Polynomial K →+* Polynomial K :=
    (Polynomial.X ^ (h * a1)).compRingHom
  have hm := complementaryLineSpecialisation_eulerScaledHessian
    (K := K) (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)
    (h := h) (k := k) (M := M) (phi := phi) hdeg
  have hsdet := congrArg Matrix.det hm
  rw [← RingHom.map_det s, ← RingHom.map_det c] at hsdet
  simpa [s, c, Polynomial.coe_compRingHom_apply] using hsdet

/-- The determinant of the Euler-scaled Hessian is the ordinary Hessian
determinant multiplied by the square of the coordinate product. -/
theorem det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant
    {K : Type*} [Field K]
    (p : MvPolynomial (Fin 4) K) :
    (eulerScaledHessian p).det =
      (∏ i : Fin 4, MvPolynomial.X i)^2 * hessianDeterminant p := by
  let D : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K) :=
    Matrix.diagonal (fun i => MvPolynomial.X i)
  let H : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) K) :=
    Matrix.transpose (hessian p)
  have hmatrix : eulerScaledHessian p = D * H * D := by
    apply Matrix.ext
    intro i j
    simp [D, H, eulerScaledHessian_apply, hessian_apply]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp [D, H, hessianDeterminant]
  ring

/-- Therefore a zero ordinary Hessian determinant gives a zero specialised
Euler-scaled determinant. -/
theorem complementaryLineSpecialisation_euler_det_zero_of_hessianDeterminant_zero
    {K : Type*} [Field K]
    {a1 a2 b1 b2 h k M : ℕ} {phi : Polynomial K}
    (hdet : hessianDeterminant
      (complementaryLinePolynomial a1 a2 b1 b2 h k M phi) = 0) :
    complementaryLineSpecialisation
      ((eulerScaledHessian
        (complementaryLinePolynomial a1 a2 b1 b2 h k M phi)).det) = 0 := by
  rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant]
  rw [hdet]
  simp

/-- A zero Hessian determinant of the actual complementary line polynomial
forces the polynomial moment determinant itself to vanish. -/
theorem complementaryPolynomialMoment_det_zero_of_hessianDeterminant_zero
    {K : Type*} [Field K] [CharZero K]
    {a1 a2 b1 b2 h k M : ℕ} {phi : Polynomial K}
    (ha1 : 0 < a1) (hh : 0 < h)
    (hdeg : phi.natDegree ≤ M)
    (hdet : hessianDeterminant
      (complementaryLinePolynomial a1 a2 b1 b2 h k M phi) = 0) :
    (complementaryPolynomialMomentHessian
      a1 a2 b1 b2 h k M phi).det = 0 := by
  have hs := complementaryLineSpecialisation_euler_det_zero_of_hessianDeterminant_zero
    (K := K) (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)
    (h := h) (k := k) (M := M) (phi := phi) hdet
  rw [complementaryLineSpecialisation_det_eulerScaledHessian
    (K := K) (a1 := a1) (a2 := a2) (b1 := b1) (b2 := b2)
    (h := h) (k := k) (M := M) (phi := phi) hdeg] at hs
  have hn : 0 < h * a1 := Nat.mul_pos hh ha1
  exact comp_X_pow_eq_zero_of_pos hn hs

/-- Mapping a zero polynomial moment determinant into the fraction field gives
exactly the Phase-72 `ComplementaryFractionMomentDetZero` predicate. -/
theorem complementaryFractionMomentDetZero_of_polynomialMoment_det_zero
    {K : Type*} [Field K] [CharZero K]
    {a1 a2 b1 b2 h k M : ℕ} {phi : Polynomial K}
    (hdet :
      (complementaryPolynomialMomentHessian
        a1 a2 b1 b2 h k M phi).det = 0) :
    ComplementaryFractionMomentDetZero
      phi (a1 : K) (a2 : K) (b1 : K) (b2 : K)
      (h : K) (k : K) (M : K) := by
  let F := FractionRing (Polynomial K)
  let ι : Polynomial K →+* F := algebraMap (Polynomial K) F
  have hmapped :
      (ι.mapMatrix (complementaryPolynomialMomentHessian
        a1 a2 b1 b2 h k M phi)).det = 0 := by
    rw [← RingHom.map_det ι]
    simpa using congrArg ι hdet
  have hbase :
      (fun i => ι (Polynomial.C
        (complementaryLogBaseExponent
          (b1 : K) (b2 : K) (k : K) (M : K) i))) =
        complementaryLogBaseExponent
          (ι (Polynomial.C (b1 : K))) (ι (Polynomial.C (b2 : K)))
          (ι (Polynomial.C (k : K))) (ι (Polynomial.C (M : K))) := by
    funext i
    fin_cases i <;>
      simp [complementaryLogBaseExponent, F, ι] <;> ring
  have hdir :
      (fun i => ι (Polynomial.C
        (complementaryLogDirection
          (a1 : K) (a2 : K) (b1 : K) (b2 : K) (h : K) (k : K) i))) =
        complementaryLogDirection
          (ι (Polynomial.C (a1 : K))) (ι (Polynomial.C (a2 : K)))
          (ι (Polynomial.C (b1 : K))) (ι (Polynomial.C (b2 : K)))
          (ι (Polynomial.C (h : K))) (ι (Polynomial.C (k : K))) := by
    funext i
    fin_cases i <;>
      simp [complementaryLogDirection, F, ι] <;> ring
  have hmat :
      ι.mapMatrix (complementaryPolynomialMomentHessian
        a1 a2 b1 b2 h k M phi) =
        lineMomentHessian
          (complementaryLogBaseExponent
            (ι (Polynomial.C (b1 : K))) (ι (Polynomial.C (b2 : K)))
            (ι (Polynomial.C (k : K))) (ι (Polynomial.C (M : K))))
          (complementaryLogDirection
            (ι (Polynomial.C (a1 : K))) (ι (Polynomial.C (a2 : K)))
            (ι (Polynomial.C (b1 : K))) (ι (Polynomial.C (b2 : K)))
            (ι (Polynomial.C (h : K))) (ι (Polynomial.C (k : K))))
          (ι phi) (ι (eulerDerivative phi))
          (ι (eulerDerivative (eulerDerivative phi))) := by
    unfold complementaryPolynomialMomentHessian
    rw [mapMatrix_lineMomentHessian]
    rw [hbase, hdir]
  unfold ComplementaryFractionMomentDetZero
  dsimp
  rw [← hmat]
  exact hmapped

/-- End-to-end local complementary-edge contradiction beginning with the
ordinary Hessian determinant of the honest multivariate line polynomial. -/
theorem complementary_line_hessian_local_impossible
    {K : Type*} [Field K] [CharZero K]
    {alpha1 alpha2 beta1 beta2 M h k m : ℕ}
    {c : K} {q : Polynomial K}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hdeg : (Polynomial.C c + Polynomial.X ^ m * q).natDegree ≤ M)
    (hdet : hessianDeterminant
      (complementaryLinePolynomial
        alpha1 alpha2 beta1 beta2 h k M
        (Polynomial.C c + Polynomial.X ^ m * q)) = 0) : False := by
  let phi : Polynomial K := Polynomial.C c + Polynomial.X ^ m * q
  have hmoment :=
    complementaryPolynomialMoment_det_zero_of_hessianDeterminant_zero
      (K := K) (a1 := alpha1) (a2 := alpha2)
      (b1 := beta1) (b2 := beta2) (h := h) (k := k) (M := M)
      (phi := phi) ha1 hh (by simpa [phi] using hdeg) (by simpa [phi] using hdet)
  have hfrac :=
    complementaryFractionMomentDetZero_of_polynomialMoment_det_zero
      (K := K) (a1 := alpha1) (a2 := alpha2)
      (b1 := beta1) (b2 := beta2) (h := h) (k := k) (M := M)
      (phi := phi) hmoment
  exact complementary_fraction_moment_local_impossible
    (K := K) ha1 ha2 hb1 hb2 hM hh hk hm hc hq0
    (by simpa [phi] using hfrac)

end

end HC4.Polynomial
