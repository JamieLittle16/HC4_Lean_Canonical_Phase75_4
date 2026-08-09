import HC4.Polynomial.AutonomousODEReconstruction
import Mathlib.Tactic

/-!
# Initial logarithmic slope from the least positive term

This file formalises the local calculation used in the complementary rank-two
edge argument.  If

    phi = c + X^m q,   m > 0,   q(0) != 0,

then `m` is the least positive exponent occurring in `phi - c`.  Put

    E = X phi'                                  (numerator of rho),
    A = X E' * phi - E^2                       (numerator of eta),

so formally

    rho = E / phi,
    eta = A / phi^2.

Consequently `eta / rho = A / (phi * E)`.  We prove purely by polynomial
coefficient algebra that the first nonzero coefficients of numerator and
denominator occur in degree `m` and that their ratio is exactly `m`.

This replaces the manuscript's local-limit statement `lim eta/rho = m` by an
exact characteristic-zero polynomial certificate.
-/

namespace HC4.Polynomial

noncomputable section

/-- The polynomial numerator of `eta = X d/dX (E/phi)` after clearing
`phi^2`, where `E = X phi'`. -/
def logarithmicEtaNumerator {K : Type*} [CommRing K]
    (phi : Polynomial K) : Polynomial K :=
  eulerDerivative (eulerDerivative phi) * phi - (eulerDerivative phi)^2

/-- The denominator that appears after dividing `eta` by `rho`:
`eta/rho = logarithmicEtaNumerator phi / (phi * eulerDerivative phi)`. -/
def logarithmicEtaOverRhoDenominator {K : Type*} [CommRing K]
    (phi : Polynomial K) : Polynomial K :=
  phi * eulerDerivative phi

/-- Euler differentiation of a shifted polynomial factors out the same power
of `X`. -/
theorem eulerDerivative_X_pow_mul
    {K : Type*} [CommRing K]
    (q : Polynomial K) (m : ℕ) :
    eulerDerivative (Polynomial.X ^ m * q) =
      Polynomial.X ^ m *
        (Polynomial.C (m : K) * q + eulerDerivative q) := by
  rcases m with _ | m
  · simp [eulerDerivative]
  · simp [eulerDerivative, Polynomial.derivative_mul,
      Polynomial.derivative_X_pow_succ] <;> ring

/-- Euler differentiation of the local form `c + X^m q` simply discards the
constant term and retains the shifted factorisation. -/
theorem eulerDerivative_local_form
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) (m : ℕ) :
    eulerDerivative (Polynomial.C c + Polynomial.X ^ m * q) =
      Polynomial.X ^ m *
        (Polynomial.C (m : K) * q + eulerDerivative q) := by
  calc
    eulerDerivative (Polynomial.C c + Polynomial.X ^ m * q) =
        eulerDerivative (Polynomial.X ^ m * q) := by
          simp [eulerDerivative, Polynomial.derivative_add]
    _ = Polynomial.X ^ m *
        (Polynomial.C (m : K) * q + eulerDerivative q) :=
      eulerDerivative_X_pow_mul q m

/-- The local form really has no correction term below degree `m`. -/
theorem coeff_lt_local_correction_zero
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) {m n : ℕ}
    (hn : n < m) :
    ((Polynomial.C c + Polynomial.X ^ m * q) - Polynomial.C c).coeff n = 0 := by
  have hnot : ¬ m ≤ n := Nat.not_le_of_gt hn
  rw [show
    (Polynomial.C c + Polynomial.X ^ m * q) - Polynomial.C c =
      Polynomial.X ^ m * q by ring]
  rw [Polynomial.coeff_X_pow_mul']
  simp [hnot]

/-- At degree `m`, the correction coefficient is exactly `q(0)`. -/
theorem coeff_local_correction_at_m
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) (m : ℕ) :
    ((Polynomial.C c + Polynomial.X ^ m * q) - Polynomial.C c).coeff m =
      q.coeff 0 := by
  rw [show
    (Polynomial.C c + Polynomial.X ^ m * q) - Polynomial.C c =
      Polynomial.X ^ m * q by ring]
  rw [Polynomial.coeff_X_pow_mul']
  simp

/-- The coefficient of `X^m` in the Euler numerator `E = X phi'` is
`m*q(0)`. -/
theorem coeff_m_eulerDerivative_local_form
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) (m : ℕ) :
    (eulerDerivative (Polynomial.C c + Polynomial.X ^ m * q)).coeff m =
      (m : K) * q.coeff 0 := by
  rw [eulerDerivative_local_form]
  rw [Polynomial.coeff_X_pow_mul']
  simp [coeff_eulerDerivative]

/-- Exact factorisation of the cleared numerator of `eta` in the local form.
The factor `X^m` makes the initial-order calculation transparent. -/
theorem logarithmicEtaNumerator_local_factor
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) (m : ℕ) :
    logarithmicEtaNumerator
        (Polynomial.C c + Polynomial.X ^ m * q) =
      Polynomial.X ^ m *
        (((Polynomial.C (m : K) *
              (Polynomial.C (m : K) * q + eulerDerivative q) +
            eulerDerivative
              (Polynomial.C (m : K) * q + eulerDerivative q)) *
            (Polynomial.C c + Polynomial.X ^ m * q)) -
          Polynomial.X ^ m *
            (Polynomial.C (m : K) * q + eulerDerivative q)^2) := by
  unfold logarithmicEtaNumerator
  rw [eulerDerivative_local_form]
  rw [eulerDerivative_X_pow_mul]
  ring

/-- The first coefficient of the cleared `eta` numerator is
`m^2 * q(0) * c`. -/
theorem coeff_m_logarithmicEtaNumerator_local_form
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) {m : ℕ} (hm : 0 < m) :
    (logarithmicEtaNumerator
        (Polynomial.C c + Polynomial.X ^ m * q)).coeff m =
      (m : K)^2 * q.coeff 0 * c := by
  rw [logarithmicEtaNumerator_local_factor]
  rw [Polynomial.coeff_X_pow_mul']
  simp only [le_refl, if_true, Nat.sub_self]
  have hshift0 : ∀ r : Polynomial K,
      (Polynomial.X ^ m * r).coeff 0 = 0 := by
    intro r
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hm]
  simp [Polynomial.mul_coeff_zero, coeff_eulerDerivative, hshift0] <;> ring

/-- The first coefficient of the denominator `phi * E` is
`c * m * q(0)`. -/
theorem coeff_m_logarithmicEtaOverRhoDenominator_local_form
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) {m : ℕ} (hm : 0 < m) :
    (logarithmicEtaOverRhoDenominator
        (Polynomial.C c + Polynomial.X ^ m * q)).coeff m =
      c * (m : K) * q.coeff 0 := by
  unfold logarithmicEtaOverRhoDenominator
  rw [eulerDerivative_local_form]
  rw [show
    (Polynomial.C c + Polynomial.X ^ m * q) *
          (Polynomial.X ^ m *
            (Polynomial.C (m : K) * q + eulerDerivative q)) =
      Polynomial.X ^ m *
        ((Polynomial.C c + Polynomial.X ^ m * q) *
          (Polynomial.C (m : K) * q + eulerDerivative q)) by ring]
  rw [Polynomial.coeff_X_pow_mul']
  simp only [le_refl, if_true, Nat.sub_self]
  have hshift0 : ∀ r : Polynomial K,
      (Polynomial.X ^ m * r).coeff 0 = 0 := by
    intro r
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hm]
  simp [Polynomial.mul_coeff_zero, coeff_eulerDerivative, hshift0] <;> ring

/-- Algebraic form of the manuscript statement `lim eta/rho = m`.

For a characteristic-zero field and a genuine least positive term
`X^m q` with `q(0) != 0`, the quotient of the first nonzero coefficients of
the cleared numerator and denominator of `eta/rho` is exactly `m`. -/
theorem logarithmic_eta_rho_initial_ratio_local_form
    {K : Type*} [Field K] [CharZero K]
    {c : K} {q : Polynomial K} {m : ℕ}
    (hm : 0 < m) (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0) :
    (logarithmicEtaNumerator
        (Polynomial.C c + Polynomial.X ^ m * q)).coeff m /
      (logarithmicEtaOverRhoDenominator
        (Polynomial.C c + Polynomial.X ^ m * q)).coeff m =
      (m : K) := by
  rw [coeff_m_logarithmicEtaNumerator_local_form c q hm,
    coeff_m_logarithmicEtaOverRhoDenominator_local_form c q hm]
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
  field_simp [hc, hq0, hmK] <;> ring

end

end HC4.Polynomial
