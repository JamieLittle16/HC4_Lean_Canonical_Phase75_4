import HC4.Polynomial.AffineEulerTwoRootDegree
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Coupling two affine two-root Euler equations at distinct affine roots

A solution of an affine two-root Euler equation with lower indicial root `j`
is divisible, after translation to the affine root, by `X^j`.  Translating
back says that the original polynomial is divisible by `(X - C alpha)^j`.

If one nonzero polynomial satisfies two such equations at distinct affine
roots, the corresponding linear factors are coprime.  Their powers therefore
multiply into the polynomial, so the sum of the two lower multiplicities is
bounded by its ordinary degree.

Combined with the adjacent-root degree bound from each equation, positive
lower roots are forced to be exactly one.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Divisibility by `X^n` after translation to `alpha` is exactly divisibility
by `(X - C alpha)^n` before translation.  Only the forward direction is needed
for the endpoint coupling. -/
theorem X_sub_C_pow_dvd_of_X_pow_dvd_translate
    (alpha : K) (phi : Polynomial K) (n : ℕ)
    (hdvd : Polynomial.X ^ n ∣ translatePolynomial alpha phi) :
    (Polynomial.X - Polynomial.C alpha) ^ n ∣ phi := by
  rcases hdvd with ⟨q, hq⟩
  refine ⟨translatePolynomial (-alpha) q, ?_⟩
  have h := congrArg (translatePolynomial (-alpha)) hq
  simpa [translatePolynomial, Polynomial.comp_assoc, sub_eq_add_neg] using h

/-- At two distinct affine roots, the two lower indicial multiplicities add to
at most the ordinary degree of a common nonzero solution. -/
theorem lowerRoot_sum_le_natDegree_of_distinct_affineTwoRoot
    (c₁ d₁ c₂ d₂ : K) (j₁ j₂ : ℕ) (phi : Polynomial K)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hphi : phi ≠ 0)
    (hzero₁ : affineTwoRootEulerOperator c₁ d₁ j₁ phi = 0)
    (hzero₂ : affineTwoRootEulerOperator c₂ d₂ j₂ phi = 0)
    (hroots : -c₁ / d₁ ≠ -c₂ / d₂) :
    j₁ + j₂ ≤ phi.natDegree := by
  let alpha : K := -c₁ / d₁
  let beta : K := -c₂ / d₂
  have htrans₁ :
      Polynomial.X ^ j₁ ∣ translatePolynomial alpha phi := by
    dsimp [alpha]
    exact X_pow_dvd_translate_of_affineTwoRoot c₁ d₁ j₁ phi hd₁ hzero₁
  have htrans₂ :
      Polynomial.X ^ j₂ ∣ translatePolynomial beta phi := by
    dsimp [beta]
    exact X_pow_dvd_translate_of_affineTwoRoot c₂ d₂ j₂ phi hd₂ hzero₂
  have hdiv₁ : (Polynomial.X - Polynomial.C alpha) ^ j₁ ∣ phi :=
    X_sub_C_pow_dvd_of_X_pow_dvd_translate alpha phi j₁ htrans₁
  have hdiv₂ : (Polynomial.X - Polynomial.C beta) ^ j₂ ∣ phi :=
    X_sub_C_pow_dvd_of_X_pow_dvd_translate beta phi j₂ htrans₂
  have hab : alpha ≠ beta := by simpa [alpha, beta] using hroots
  have hunit : IsUnit (alpha - beta) := (sub_ne_zero.mpr hab).isUnit
  have hcopBase :
      IsCoprime (Polynomial.X - Polynomial.C alpha)
        (Polynomial.X - Polynomial.C beta) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit
  have hcop :
      IsCoprime ((Polynomial.X - Polynomial.C alpha) ^ j₁)
        ((Polynomial.X - Polynomial.C beta) ^ j₂) :=
    hcopBase.pow
  have hprod :
      (Polynomial.X - Polynomial.C alpha) ^ j₁ *
          (Polynomial.X - Polynomial.C beta) ^ j₂ ∣ phi :=
    hcop.mul_dvd hdiv₁ hdiv₂
  have hdeg := Polynomial.natDegree_le_of_dvd hprod hphi
  simpa using hdeg

/-- Consequently, if both lower indicial roots are positive, two distinct
affine roots force both of them to equal one. -/
theorem lowerRoots_eq_one_of_distinct_affineTwoRoot
    (c₁ d₁ c₂ d₂ : K) (j₁ j₂ : ℕ) (phi : Polynomial K)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hj₁ : 0 < j₁) (hj₂ : 0 < j₂)
    (hphi : phi ≠ 0)
    (hzero₁ : affineTwoRootEulerOperator c₁ d₁ j₁ phi = 0)
    (hzero₂ : affineTwoRootEulerOperator c₂ d₂ j₂ phi = 0)
    (hroots : -c₁ / d₁ ≠ -c₂ / d₂) :
    j₁ = 1 ∧ j₂ = 1 := by
  have hsum := lowerRoot_sum_le_natDegree_of_distinct_affineTwoRoot
    c₁ d₁ c₂ d₂ j₁ j₂ phi hd₁ hd₂ hphi hzero₁ hzero₂ hroots
  have hdeg₁ := natDegree_eq_root_or_succ_of_affineTwoRoot
    c₁ d₁ j₁ phi hd₁ hphi hzero₁
  have hdeg₂ := natDegree_eq_root_or_succ_of_affineTwoRoot
    c₂ d₂ j₂ phi hd₂ hphi hzero₂
  have hle₁ : phi.natDegree ≤ j₁ + 1 := by
    rcases hdeg₁ with h | h <;> omega
  have hle₂ : phi.natDegree ≤ j₂ + 1 := by
    rcases hdeg₂ with h | h <;> omega
  omega

end

end HC4.Polynomial
