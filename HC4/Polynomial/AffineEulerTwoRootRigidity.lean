import HC4.Polynomial.AutonomousODETranslation
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# Two-root affine Euler ODE rigidity

The first Hessian variation of a primitive rank-three binomial against a lower
parallel fibre produces, after translating the unique root of an affine linear
form to the origin, the elementary Euler equation

    X^2 phi'' - 2*j*X*phi' + j*(j+1)*phi = 0.

Writing `E = X d/dX`, this is

    E(E phi) - (2*j+1) E phi + j*(j+1) phi = 0.

Its coefficient at `X^m` is

    (m-j)(m-j-1) phi_m.

In characteristic zero the translated polynomial is therefore supported only
in degrees `j` and `j+1`.  In particular it is divisible by `X^j`.

The second half of the file transports the statement back through a general
affine form `c + d X`, `d != 0`.  This is state-free polynomial algebra; no
Newton, valuation, clock, or HC4 state object occurs here.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Euler operator whose indicial roots are the adjacent integers `j,j+1`. -/
def twoRootEulerOperator (j : ℕ) (phi : Polynomial K) : Polynomial K :=
  eulerDerivative (eulerDerivative phi) -
      Polynomial.C (((2 * j + 1 : ℕ) : K)) * eulerDerivative phi +
    Polynomial.C (((j * (j + 1) : ℕ) : K)) * phi

/-- Exact coefficient factorisation of the two-root Euler operator. -/
theorem coeff_twoRootEulerOperator
    (j m : ℕ) (phi : Polynomial K) :
    (twoRootEulerOperator j phi).coeff m =
      ((m : K) - (j : K)) *
        ((m : K) - ((j + 1 : ℕ) : K)) * phi.coeff m := by
  unfold twoRootEulerOperator
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, coeff_eulerDerivative]
  push_cast
  ring

/-- A nonzero coefficient of a solution can occur only at the two indicial
roots. -/
theorem support_twoRootEulerOperator_eq_zero
    (j : ℕ) (phi : Polynomial K)
    (hzero : twoRootEulerOperator j phi = 0) :
    ∀ {m : ℕ}, m ∈ phi.support → m = j ∨ m = j + 1 := by
  intro m hm
  have hmne : phi.coeff m ≠ 0 := Polynomial.mem_support_iff.mp hm
  have hc := congrArg (fun p : Polynomial K => p.coeff m) hzero
  rw [coeff_twoRootEulerOperator] at hc
  simp only [Polynomial.coeff_zero] at hc
  have hscalar :
      ((m : K) - (j : K)) *
        ((m : K) - ((j + 1 : ℕ) : K)) = 0 :=
    (mul_eq_zero.mp (by simpa [mul_assoc] using hc)).resolve_right hmne
  rcases mul_eq_zero.mp hscalar with hleft | hright
  · left
    have hcast : (m : K) = (j : K) := sub_eq_zero.mp hleft
    exact_mod_cast hcast
  · right
    have hcast : (m : K) = ((j + 1 : ℕ) : K) := sub_eq_zero.mp hright
    exact_mod_cast hcast

/-- The whole support of a two-root solution lies in `{j,j+1}`. -/
theorem twoRootEulerOperator_support_subset
    (j : ℕ) (phi : Polynomial K)
    (hzero : twoRootEulerOperator j phi = 0) :
    phi.support ⊆ {j, j + 1} := by
  intro m hm
  rcases support_twoRootEulerOperator_eq_zero j phi hzero hm with h | h
  · simp [h]
  · simp [h]

/-- Every solution is divisible by the lower indicial power `X^j`. -/
theorem X_pow_dvd_of_twoRootEulerOperator_eq_zero
    (j : ℕ) (phi : Polynomial K)
    (hzero : twoRootEulerOperator j phi = 0) :
    Polynomial.X ^ j ∣ phi := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  by_contra hcoeff
  have hsupp : m ∈ phi.support := Polynomial.mem_support_iff.mpr hcoeff
  rcases support_twoRootEulerOperator_eq_zero j phi hzero hsupp with h | h
  · omega
  · omega

/-- A nonzero solution has degree at most `j+1`. -/
theorem natDegree_le_succ_of_twoRootEulerOperator_eq_zero
    (j : ℕ) (phi : Polynomial K)
    (hzero : twoRootEulerOperator j phi = 0) :
    phi.natDegree ≤ j + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  by_contra hcoeff
  have hsupp : m ∈ phi.support := Polynomial.mem_support_iff.mpr hcoeff
  rcases support_twoRootEulerOperator_eq_zero j phi hzero hsupp with h | h
  · omega
  · omega

/-- The affine linear form used before translation. -/
def affineEulerLinear (c d : K) : Polynomial K :=
  Polynomial.C c + Polynomial.C d * Polynomial.X

/-- Ordinary-derivative form of the affine Euler equation with roots `j,j+1`. -/
def affineTwoRootEulerOperator
    (c d : K) (j : ℕ) (phi : Polynomial K) : Polynomial K :=
  affineEulerLinear c d ^ 2 * phi.derivative.derivative -
    Polynomial.C (((2 * j : ℕ) : K) * d) *
        affineEulerLinear c d * phi.derivative +
    Polynomial.C (((j * (j + 1) : ℕ) : K) * d ^ 2) * phi

/-- The affine form translates to `d*X` at its root `-c/d`. -/
theorem translatePolynomial_affineEulerLinear_root
    (c d : K) (hd : d ≠ 0) :
    translatePolynomial (-c / d) (affineEulerLinear c d) =
      Polynomial.C d * Polynomial.X := by
  unfold translatePolynomial affineEulerLinear
  simp only [Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp]
  have hroot : c + d * (-c / d) = 0 := by
    field_simp
  rw [show
      Polynomial.C c + Polynomial.C d *
          (Polynomial.X + Polynomial.C (-c / d)) =
        Polynomial.C (c + d * (-c / d)) + Polynomial.C d * Polynomial.X by
      simp only [map_add, map_mul]
      ring]
  rw [hroot]
  simp

/-- Translating the affine equation to the root gives the normalized Euler
operator, up to the harmless nonzero scalar `d^2`. -/
theorem twoRootEulerOperator_translate_of_affineTwoRoot
    (c d : K) (j : ℕ) (phi : Polynomial K)
    (hd : d ≠ 0)
    (hzero : affineTwoRootEulerOperator c d j phi = 0) :
    twoRootEulerOperator j (translatePolynomial (-c / d) phi) = 0 := by
  let alpha : K := -c / d
  let psi : Polynomial K := translatePolynomial alpha phi
  have htrans := congrArg (translatePolynomial alpha) hzero
  have hL : translatePolynomial alpha (affineEulerLinear c d) =
      Polynomial.C d * Polynomial.X := by
    dsimp [alpha]
    exact translatePolynomial_affineEulerLinear_root c d hd
  have hd1 :
      translatePolynomial alpha phi.derivative = psi.derivative := by
    dsimp [psi]
    exact (derivative_translatePolynomial alpha phi).symm
  have hd2 :
      translatePolynomial alpha phi.derivative.derivative =
        psi.derivative.derivative := by
    dsimp [psi]
    rw [derivative_translatePolynomial alpha phi,
      derivative_translatePolynomial alpha (Polynomial.derivative phi)]
  have hscaled :
      Polynomial.C (d ^ 2) * twoRootEulerOperator j psi = 0 := by
    unfold affineTwoRootEulerOperator at htrans
    simp only [translatePolynomial, Polynomial.zero_comp,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp, Polynomial.C_comp] at htrans
    fold translatePolynomial at htrans
    rw [hL, hd1, hd2] at htrans
    unfold twoRootEulerOperator eulerDerivative
    simp only [Polynomial.derivative_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, mul_one, mul_zero, add_zero,
      Polynomial.C_mul, Polynomial.C_pow]
    push_cast
    ring_nf at htrans ⊢
    exact htrans
  have hC : (Polynomial.C (d ^ 2) : Polynomial K) ≠ 0 := by
    exact Polynomial.C_ne_zero.mpr (pow_ne_zero 2 hd)
  exact (mul_eq_zero.mp hscaled).resolve_left hC

/-- Hence the translated affine solution is supported only at the adjacent
powers `j,j+1`. -/
theorem translated_support_subset_of_affineTwoRoot
    (c d : K) (j : ℕ) (phi : Polynomial K)
    (hd : d ≠ 0)
    (hzero : affineTwoRootEulerOperator c d j phi = 0) :
    (translatePolynomial (-c / d) phi).support ⊆ {j, j + 1} :=
  twoRootEulerOperator_support_subset j _
    (twoRootEulerOperator_translate_of_affineTwoRoot c d j phi hd hzero)

/-- In particular the translated polynomial has a root of multiplicity at
least `j` at the origin. -/
theorem X_pow_dvd_translate_of_affineTwoRoot
    (c d : K) (j : ℕ) (phi : Polynomial K)
    (hd : d ≠ 0)
    (hzero : affineTwoRootEulerOperator c d j phi = 0) :
    Polynomial.X ^ j ∣ translatePolynomial (-c / d) phi :=
  X_pow_dvd_of_twoRootEulerOperator_eq_zero j _
    (twoRootEulerOperator_translate_of_affineTwoRoot c d j phi hd hzero)

end

end HC4.Polynomial
