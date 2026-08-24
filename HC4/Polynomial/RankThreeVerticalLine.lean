import HC4.Polynomial.RankThreeMvMomentRealisation
import Mathlib.Tactic

/-!
# A18.5.10: honest vertical rank-three lines

The terminal aligned-Smith source geometry naturally produces a different
rank-three line from the finite endpoint interpolation used in A18.5.4.
Its three transverse exponents are fixed while only the longitudinal exponent
moves.  Thus the honest polynomial has the form

    x₁^b x₂^c x₃^d * φ(x₀).

This file records that polynomial directly, without forcing the fixed
transverse exponent through the auxiliary segment length `M` of A18.5.4.
When `b,c,d > 0`, the constant term of `φ` is the genuine rank-three endpoint
`(0,b,c,d)`, and every positive degree of `φ` leaves the omitted coordinate.

The model is deliberately elementary: each coefficient of `φ` is realised by
one genuine `MvPolynomial` monomial, and the standard rank-three
specialisation `x₀ = X`, `x₁=x₂=x₃=1` recovers `φ` literally.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- Honest exponent of the `j`th term on a vertical rank-three line. -/
def rankThreeVerticalExponentFinsupp
    (b c d j : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (0 : Fin 4) j +
    Finsupp.single (1 : Fin 4) b +
    Finsupp.single (2 : Fin 4) c +
    Finsupp.single (3 : Fin 4) d

@[simp] theorem rankThreeVerticalExponentFinsupp_apply
    (b c d j : ℕ) (i : Fin 4) :
    rankThreeVerticalExponentFinsupp b c d j i = ![j, b, c, d] i := by
  fin_cases i <;>
    simp [rankThreeVerticalExponentFinsupp, add_assoc]

/-- Coefficient-field exponent vector of the same honest monomial. -/
def rankThreeVerticalExponentValue
    {K : Type*} [NatCast K]
    (b c d j : ℕ) : Fin 4 → K :=
  ![(j : K), (b : K), (c : K), (d : K)]

/-- Casting the honest natural exponent gives the displayed coefficient-field
vector. -/
theorem rankThreeVerticalExponentFinsupp_cast
    {K : Type*} [Field K] [CharZero K]
    (b c d j : ℕ) (i : Fin 4) :
    ((rankThreeVerticalExponentFinsupp b c d j i : ℕ) : K) =
      rankThreeVerticalExponentValue (K := K) b c d j i := by
  fin_cases i <;>
    simp [rankThreeVerticalExponentFinsupp,
      rankThreeVerticalExponentValue]

/-- One honest monomial on the vertical line. -/
def rankThreeVerticalTerm
    {K : Type*} [CommSemiring K]
    (b c d j : ℕ) (a : K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.C a *
    MvPolynomial.X (0 : Fin 4) ^ j *
    MvPolynomial.X (1 : Fin 4) ^ b *
    MvPolynomial.X (2 : Fin 4) ^ c *
    MvPolynomial.X (3 : Fin 4) ^ d

/-- The product presentation is literally the monomial at the vertical-line
exponent. -/
theorem rankThreeVerticalTerm_eq_monomial
    {K : Type*} [Field K]
    (b c d j : ℕ) (a : K) :
    rankThreeVerticalTerm b c d j a =
      MvPolynomial.monomial (rankThreeVerticalExponentFinsupp b c d j) a := by
  simp only [rankThreeVerticalTerm, MvPolynomial.X_pow_eq_monomial]
  rw [MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  rw [MvPolynomial.monomial_mul]
  simp only [mul_one]
  apply congrArg (fun e => MvPolynomial.monomial e a)
  ext i
  fin_cases i <;>
    simp [rankThreeVerticalExponentFinsupp, add_assoc]

/-- Honest multivariate polynomial attached to one univariate vertical
coefficient fibre. -/
def rankThreeVerticalPolynomial
    {K : Type*} [CommSemiring K]
    (b c d : ℕ) (phi : Polynomial K) : MvPolynomial (Fin 4) K :=
  phi.sum fun j a => rankThreeVerticalTerm b c d j a

/-- One vertical term specialises back to its original univariate monomial. -/
theorem rankThreeLineSpecialisation_verticalTerm
    {K : Type*} [CommSemiring K]
    (b c d j : ℕ) (a : K) :
    rankThreeLineSpecialisation (rankThreeVerticalTerm b c d j a) =
      Polynomial.C a * Polynomial.X ^ j := by
  simp [rankThreeLineSpecialisation, rankThreeVerticalTerm]

/-- The standard rank-three specialisation recovers the coefficient polynomial
literally; there is no `X ↦ X^u` reindexing in the vertical model. -/
theorem rankThreeLineSpecialisation_verticalPolynomial
    {K : Type*} [CommSemiring K]
    (b c d : ℕ) (phi : Polynomial K) :
    rankThreeLineSpecialisation (rankThreeVerticalPolynomial b c d phi) = phi := by
  rw [Polynomial.as_sum phi]
  simp only [rankThreeVerticalPolynomial, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rankThreeLineSpecialisation_verticalTerm]

/-- Consequently the honest vertical-line construction is injective in its
univariate coefficient polynomial. -/
theorem rankThreeVerticalPolynomial_injective
    {K : Type*} [Field K]
    (b c d : ℕ) :
    Function.Injective
      (rankThreeVerticalPolynomial (K := K) b c d) := by
  intro phi psi h
  have hs := congrArg rankThreeLineSpecialisation h
  simpa [rankThreeLineSpecialisation_verticalPolynomial] using hs

/-- Euler differentiation of a vertical term multiplies it by its honest
source exponent. -/
theorem mvEuler_rankThreeVerticalTerm
    {K : Type*} [Field K] [CharZero K]
    (b c d j : ℕ) (a : K) (i : Fin 4) :
    mvEuler i (rankThreeVerticalTerm b c d j a) =
      MvPolynomial.C
          (rankThreeVerticalExponentValue (K := K) b c d j i) *
        rankThreeVerticalTerm b c d j a := by
  rw [rankThreeVerticalTerm_eq_monomial]
  unfold mvEuler
  rw [MvPolynomial.X_mul_pderiv_monomial]
  rw [← rankThreeVerticalTerm_eq_monomial]
  rw [← rankThreeVerticalExponentFinsupp_cast (K := K)]
  simp [nsmul_eq_mul]

/-- Euler-scaled Hessian of one vertical term has the expected exponent-core
coefficient. -/
theorem eulerScaledHessian_rankThreeVerticalTerm
    {K : Type*} [Field K] [CharZero K]
    (b c d j : ℕ) (a : K) (i l : Fin 4) :
    eulerScaledHessian (rankThreeVerticalTerm b c d j a) i l =
      MvPolynomial.C
          (rankThreeVerticalExponentValue (K := K) b c d j i *
            rankThreeVerticalExponentValue (K := K) b c d j l -
            if i = l then
              rankThreeVerticalExponentValue (K := K) b c d j i
            else 0) *
        rankThreeVerticalTerm b c d j a := by
  change
    mvEuler i (mvEuler l (rankThreeVerticalTerm b c d j a)) -
        (if i = l then mvEuler i (rankThreeVerticalTerm b c d j a) else 0) = _
  rw [mvEuler_rankThreeVerticalTerm (K := K) b c d j a l]
  rw [mvEuler_C_mul]
  rw [mvEuler_rankThreeVerticalTerm (K := K) b c d j a i]
  by_cases hil : i = l
  · subst l
    simp [MvPolynomial.C_mul, MvPolynomial.C_sub]
    ring
  · simp [hil, MvPolynomial.C_mul]
    ring

end

end HC4.Polynomial
