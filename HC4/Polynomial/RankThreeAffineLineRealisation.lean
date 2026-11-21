import HC4.Polynomial.RankThreeMvMomentRealisation
import Mathlib.Tactic

/-!
# A18.5.24: a general honest affine rank-three line

A18.5.4 used the special finite-segment exponents `(M-j)v + j u`.  That is
perfect for the binomial endpoint after ODE reconstruction, but an arbitrary
Newton edge need not have its endpoint exponents divisible by the number of
coefficient layers.

For the pre-ODE edge we only need the actual fact used by logarithmic Hessian
moments: on every supported coefficient index `j`, the honest natural exponent
vector casts to an affine line

    v + j w,

where `v=(0,A,B,C)` is a genuine rank-three exponent and the omitted-coordinate
direction is the positive natural integer `u1`.  The other direction entries
are allowed to be arbitrary field elements; this accommodates decreasing
source exponents without introducing Laurent monomials.

The structure below stores exactly that support-indexed affine identity.  Its
associated `MvPolynomial` is completely honest, and specialisation
`x0=X, x1=x2=x3=1` sends the `j`th term to `c_j X^(j*u1)`.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- Honest exponent data for a finite rank-three affine support line. -/
structure RankThreeAffineLineData
    {K : Type*} [Field K] [CharZero K]
    (A B C u1 : ℕ) (q r s : K) (phi : Polynomial K) where
  exponent : ℕ → (Fin 4 →₀ ℕ)
  affine :
    ∀ j ∈ phi.support,
      (fun i : Fin 4 => ((exponent j i : ℕ) : K)) =
        fun i =>
          rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
            (j : K) * rankThreeLogDirection (u1 : K) q r s i

/-- The omitted-coordinate exponent of the `j`th supported monomial is
literally `j*u1`. -/
theorem RankThreeAffineLineData.exponent_zero_eq
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    {j : ℕ} (hj : j ∈ phi.support) :
    L.exponent j (0 : Fin 4) = j * u1 := by
  have h := congrFun (L.affine j hj) (0 : Fin 4)
  have h' :
      ((L.exponent j (0 : Fin 4) : ℕ) : K) =
        (((j * u1 : ℕ) : K)) := by
    simpa [rankThreeLogBaseExponent, rankThreeLogDirection,
      Nat.cast_mul] using h
  exact_mod_cast h'

/-- Honest product presentation of one affine-line monomial. -/
def RankThreeAffineLineData.term
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (j : ℕ) (c : K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.C c *
    MvPolynomial.X (0 : Fin 4) ^ (L.exponent j 0) *
    MvPolynomial.X (1 : Fin 4) ^ (L.exponent j 1) *
    MvPolynomial.X (2 : Fin 4) ^ (L.exponent j 2) *
    MvPolynomial.X (3 : Fin 4) ^ (L.exponent j 3)

/-- The product presentation is the literal monomial at `L.exponent j`. -/
theorem RankThreeAffineLineData.term_eq_monomial
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (j : ℕ) (c : K) :
    L.term j c = MvPolynomial.monomial (L.exponent j) c := by
  simp only [RankThreeAffineLineData.term, MvPolynomial.X_pow_eq_monomial]
  rw [MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  simp only [mul_one]
  apply congrArg (fun d => MvPolynomial.monomial d c)
  ext i
  fin_cases i <;> simp [add_assoc]

/-- Actual multivariate polynomial represented by the support-indexed affine
line. -/
def RankThreeAffineLineData.polynomial
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi) :
    MvPolynomial (Fin 4) K :=
  phi.sum fun j c => L.term j c

/-- Euler differentiation of one honest affine-line term multiplies it by its
actual exponent. -/
theorem RankThreeAffineLineData.mvEuler_term
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (j : ℕ) (c : K) (i : Fin 4) :
    mvEuler i (L.term j c) =
      MvPolynomial.C ((L.exponent j i : ℕ) : K) * L.term j c := by
  rw [L.term_eq_monomial]
  unfold mvEuler
  rw [MvPolynomial.X_mul_pderiv_monomial]
  rw [← L.term_eq_monomial]
  simp [nsmul_eq_mul]

/-- Euler-scaled Hessian of one affine-line term. -/
theorem RankThreeAffineLineData.eulerScaledHessian_term
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    (j : ℕ) (c : K) (i l : Fin 4) :
    eulerScaledHessian (L.term j c) i l =
      MvPolynomial.C
          ((((L.exponent j i : ℕ) : K) * ((L.exponent j l : ℕ) : K)) -
            if i = l then ((L.exponent j i : ℕ) : K) else 0) *
        L.term j c := by
  change
    mvEuler i (mvEuler l (L.term j c)) -
        (if i = l then mvEuler i (L.term j c) else 0) = _
  rw [L.mvEuler_term j c l]
  rw [mvEuler_C_mul]
  rw [L.mvEuler_term j c i]
  by_cases hil : i = l
  · subst l
    simp [MvPolynomial.C_mul, MvPolynomial.C_sub]
    ring
  · simp [hil, MvPolynomial.C_mul]
    ring

/-- The standard rank-three specialisation of one supported affine term. -/
theorem RankThreeAffineLineData.specialisation_term
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    {j : ℕ} (hj : j ∈ phi.support) (c : K) :
    rankThreeLineSpecialisation (L.term j c) =
      Polynomial.C c * Polynomial.X ^ (j * u1) := by
  simp [RankThreeAffineLineData.term, rankThreeLineSpecialisation,
    L.exponent_zero_eq hj]

/-- Specialised Euler-Hessian formula for one supported affine-line term. -/
theorem RankThreeAffineLineData.specialisation_eulerScaledHessian_term
    {K : Type*} [Field K] [CharZero K]
    {A B C u1 : ℕ} {q r s : K} {phi : Polynomial K}
    (L : RankThreeAffineLineData A B C u1 q r s phi)
    {j : ℕ} (hj : j ∈ phi.support) (c : K) (i l : Fin 4) :
    rankThreeLineSpecialisation
        (eulerScaledHessian (L.term j c) i l) =
      Polynomial.C
          ((rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
                (j : K) * rankThreeLogDirection (u1 : K) q r s i) *
            (rankThreeLogBaseExponent (A : K) (B : K) (C : K) l +
                (j : K) * rankThreeLogDirection (u1 : K) q r s l) -
            if i = l then
              rankThreeLogBaseExponent (A : K) (B : K) (C : K) i +
                (j : K) * rankThreeLogDirection (u1 : K) q r s i
            else 0) *
        (Polynomial.C c * Polynomial.X ^ (j * u1)) := by
  rw [L.eulerScaledHessian_term]
  rw [map_mul]
  rw [L.specialisation_term hj]
  have haff := L.affine j hj
  have hi := congrFun haff i
  have hl := congrFun haff l
  rw [hi, hl]
  simp [rankThreeLineSpecialisation]

end

end HC4.Polynomial
