import HC4.Polynomial.ComplementaryLogHessian
import HC4.Polynomial.LogarithmicInitialSlope
import Mathlib.Tactic

/-!
# Assembly of the complementary rank-two endpoint obstruction

The previous files certify two independent pieces of the manuscript argument:

* the complementary logarithmic Hessian determinant and its rational
  `eta`-equation;
* the initial logarithmic slope attached to a local form
  `phi = c + X^m q`.

This file joins them algebraically.  No limits are used.

After writing

    E = X phi',
    A = X E' * phi - E^2,

we have formally `rho = E/phi` and `eta = A/phi^2`.  Clearing denominators in

    eta = rho (M-rho) (r0 + r1 rho) / (d0 + d1 rho)

gives

    A (d0 phi + d1 E)
      = E (M phi - E) (r0 phi + r1 E).

For a genuine least positive term `phi = c + X^m q`, comparison of the first
nonzero coefficient forces `m = 1/(A0*h)`, which is arithmetically impossible
when `A0` is the sum of two positive exponents.
-/

namespace HC4.Polynomial

noncomputable section

/-- The denominator-cleared complementary `eta` equation after substituting
`rho = E/phi` and `eta = A/phi^2`, where `E = X phi'` and
`A = X E' * phi - E^2`. -/
def ComplementaryClearedEquation
    {K : Type*} [CommRing K]
    (phi : Polynomial K) (A0 B0 M h k : K) : Prop :=
  let E := eulerDerivative phi
  logarithmicEtaNumerator phi *
      (Polynomial.C (A0 * M * h * (B0 * M * k - 1)) * phi +
        Polynomial.C (A0 * h - B0 * k) * E) =
    E * (Polynomial.C M * phi - E) *
      (Polynomial.C (B0 * M * k - 1) * phi +
        Polynomial.C (A0 * h - B0 * k) * E)

/-- A zero complementary logarithmic-Hessian determinant gives the scalar
rational `eta` equation once its universal prefactor is known to be nonzero. -/
theorem complementary_eta_equation_of_det_zero
    {K : Type*} [Field K]
    {a1 a2 b1 b2 h k M rho eta : K}
    (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0)
    (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0)
    (hh : h ≠ 0) (hk : k ≠ 0)
    (hrho : rho ≠ 0) (hMrho : M - rho ≠ 0)
    (hdet :
      (complementaryLogHessianCore
        a1 a2 b1 b2 h k M rho eta).det = 0) :
    ((a1 + a2) * (b1 + b2) * M^2 * h * k
        - (a1 + a2) * M * h
        + ((a1 + a2) * h - (b1 + b2) * k) * rho) * eta =
      rho * (M - rho) *
        ((b1 + b2) * M * k
          + ((a1 + a2) * h - (b1 + b2) * k) * rho - 1) := by
  rw [det_complementaryLogHessianCore] at hdet
  have hpref :
      a1 * a2 * b1 * b2 * h^2 * k^2 * rho * (M - rho) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero
                (mul_ne_zero ha1 ha2) hb1) hb2)
              (pow_ne_zero 2 hh))
            (pow_ne_zero 2 hk))
          hrho)
        hMrho
  have hbracket :
      (((a1 + a2) * (b1 + b2) * M^2 * h * k
          - (a1 + a2) * M * h
          + ((a1 + a2) * h - (b1 + b2) * k) * rho) * eta
        - rho * (M - rho) *
          ((b1 + b2) * M * k
            + ((a1 + a2) * h - (b1 + b2) * k) * rho - 1)) = 0 :=
    (mul_eq_zero.mp hdet).resolve_left hpref
  exact sub_eq_zero.mp hbracket

/-- The cleared complementary equation and a genuine local least-positive term
force the manuscript endpoint equality `m = 1/(A0*h)`.

This is the exact algebraic replacement for comparing the two limits
`eta/rho -> m` and `eta/rho -> 1/(A0*h)`. -/
theorem complementary_cleared_equation_forces_initial_ratio
    {K : Type*} [Field K] [CharZero K]
    {c A0 B0 M h k : K} {q : Polynomial K} {m : ℕ}
    (hm : 0 < m) (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hA0 : A0 ≠ 0) (hM : M ≠ 0) (hh : h ≠ 0)
    (hres : B0 * M * k - 1 ≠ 0)
    (hEq : ComplementaryClearedEquation
      (Polynomial.C c + Polynomial.X ^ m * q) A0 B0 M h k) :
    (m : K) = 1 / (A0 * h) := by
  let phi : Polynomial K := Polynomial.C c + Polynomial.X ^ m * q
  let G : Polynomial K := Polynomial.C (m : K) * q + eulerDerivative q
  let H : Polynomial K :=
    ((Polynomial.C (m : K) * G + eulerDerivative G) * phi -
      Polynomial.X ^ m * G^2)

  have hE : eulerDerivative phi = Polynomial.X ^ m * G := by
    dsimp [phi, G]
    exact eulerDerivative_local_form c q m

  have hA : logarithmicEtaNumerator phi = Polynomial.X ^ m * H := by
    dsimp [phi, G, H]
    exact logarithmicEtaNumerator_local_factor c q m

  have hG0 : G.coeff 0 = (m : K) * q.coeff 0 := by
    have h := coeff_m_eulerDerivative_local_form c q m
    rw [show eulerDerivative
        (Polynomial.C c + Polynomial.X ^ m * q) =
          Polynomial.X ^ m * G by simpa [phi] using hE] at h
    rw [Polynomial.coeff_X_pow_mul'] at h
    simpa using h

  have hH0 : H.coeff 0 = (m : K)^2 * q.coeff 0 * c := by
    have h := coeff_m_logarithmicEtaNumerator_local_form c q hm
    rw [show logarithmicEtaNumerator
        (Polynomial.C c + Polynomial.X ^ m * q) =
          Polynomial.X ^ m * H by simpa [phi] using hA] at h
    rw [Polynomial.coeff_X_pow_mul'] at h
    simpa using h

  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hphi0 : phi.coeff 0 = c := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [phi, hm0]

  unfold ComplementaryClearedEquation at hEq
  change logarithmicEtaNumerator phi *
      (Polynomial.C (A0 * M * h * (B0 * M * k - 1)) * phi +
        Polynomial.C (A0 * h - B0 * k) * eulerDerivative phi) =
    eulerDerivative phi * (Polynomial.C M * phi - eulerDerivative phi) *
      (Polynomial.C (B0 * M * k - 1) * phi +
        Polynomial.C (A0 * h - B0 * k) * eulerDerivative phi) at hEq
  rw [hA, hE] at hEq

  have hfactored :
      Polynomial.X ^ m *
        (H *
          (Polynomial.C (A0 * M * h * (B0 * M * k - 1)) * phi +
            Polynomial.C (A0 * h - B0 * k) *
              (Polynomial.X ^ m * G))) =
      Polynomial.X ^ m *
        (G *
          (Polynomial.C M * phi - Polynomial.X ^ m * G) *
          (Polynomial.C (B0 * M * k - 1) * phi +
            Polynomial.C (A0 * h - B0 * k) *
              (Polynomial.X ^ m * G))) := by
    simpa only [mul_assoc] using hEq

  have hcoeffRaw := congrArg (fun p : Polynomial K => p.coeff m) hfactored
  have hcoeff :
      (H *
        (Polynomial.C (A0 * M * h * (B0 * M * k - 1)) * phi +
          Polynomial.C (A0 * h - B0 * k) * (Polynomial.X ^ m * G))).coeff 0 =
      (G * (Polynomial.C M * phi - Polynomial.X ^ m * G) *
        (Polynomial.C (B0 * M * k - 1) * phi +
          Polynomial.C (A0 * h - B0 * k) * (Polynomial.X ^ m * G))).coeff 0 := by
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, if_true, Nat.sub_self] using hcoeffRaw
  rw [Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_zero_eq_eval_zero] at hcoeff

  have hG_eval : Polynomial.eval 0 G = (m : K) * q.coeff 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hG0
  have hH_eval : Polynomial.eval 0 H = (m : K)^2 * q.coeff 0 * c := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hH0
  have hphi_eval : Polynomial.eval 0 phi = c := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hphi0
  have hXm_eval : Polynomial.eval 0 (Polynomial.X ^ m : Polynomial K) = 0 := by
    simp [Nat.ne_of_gt hm]

  simp [hG_eval, hH_eval, hphi_eval, hXm_eval] at hcoeff

  let common : K :=
    (m : K) * q.coeff 0 * M * (B0 * M * k - 1) * c^2
  have hscaled : common * ((m : K) * A0 * h) = common := by
    dsimp [common]
    linear_combination hcoeff

  have hmK : (m : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hcommon : common ≠ 0 := by
    dsimp [common]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero hmK hq0)
          hM)
        hres)
      (pow_ne_zero 2 hc)

  have hzero : common * (((m : K) * A0 * h) - 1) = 0 := by
    calc
      common * (((m : K) * A0 * h) - 1) =
          common * ((m : K) * A0 * h) - common := by ring
      _ = 0 := sub_eq_zero.mpr hscaled
  have hmh_sub : ((m : K) * A0 * h) - 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hcommon
  have hmh : (m : K) * A0 * h = 1 := sub_eq_zero.mp hmh_sub
  have hAh : A0 * h ≠ 0 := mul_ne_zero hA0 hh
  apply (eq_div_iff hAh).2
  simpa [mul_assoc] using hmh

/-- Natural-exponent endpoint form.  If both complementary blocks contain two
positive exponents and `m,h,M,k` are positive, the cleared complementary
identity cannot hold for a genuine local least-positive term. -/
theorem complementary_cleared_equation_impossible
    {K : Type*} [Field K] [CharZero K]
    {alpha1 alpha2 beta1 beta2 M h k m : ℕ}
    {c : K} {q : Polynomial K}
    (ha1 : 0 < alpha1) (ha2 : 0 < alpha2)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2)
    (hM : 0 < M) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hEq : ComplementaryClearedEquation
      (Polynomial.C c + Polynomial.X ^ m * q)
      ((alpha1 + alpha2 : ℕ) : K)
      ((beta1 + beta2 : ℕ) : K)
      (M : K) (h : K) (k : K)) : False := by
  have hA0nat : 2 ≤ alpha1 + alpha2 := by omega
  have hB0nat : 2 ≤ beta1 + beta2 := by omega
  have hM1 : 1 ≤ M := Nat.succ_le_iff.mpr hM
  have hk1 : 1 ≤ k := Nat.succ_le_iff.mpr hk
  have hresnat : (beta1 + beta2) * M * k ≠ 1 := by
    have htwo : 2 ≤ (beta1 + beta2) * M * k := by
      calc
        2 = 2 * 1 * 1 := by norm_num
        _ ≤ (beta1 + beta2) * M * k :=
          Nat.mul_le_mul (Nat.mul_le_mul hB0nat hM1) hk1
    omega

  have hA0K : (((alpha1 + alpha2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hA0nat))
  have hMK : (M : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hhK : (h : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  have hrescast : ((((beta1 + beta2) * M * k : ℕ) : K)) ≠ 1 := by
    exact_mod_cast hresnat
  have hresK :
      ((beta1 + beta2 : ℕ) : K) * (M : K) * (k : K) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    simpa [Nat.cast_add, Nat.cast_mul, mul_assoc] using hrescast

  have hlimK :=
    complementary_cleared_equation_forces_initial_ratio
      (K := K) hm hc hq0 hA0K hMK hhK hresK hEq

  have hAhK :
      ((alpha1 + alpha2 : ℕ) : K) * (h : K) ≠ 0 :=
    mul_ne_zero hA0K hhK
  have hmulK :
      (m : K) * (((alpha1 + alpha2 : ℕ) : K) * (h : K)) = 1 :=
    (eq_div_iff hAhK).mp hlimK
  have hcast :
      ((m * ((alpha1 + alpha2) * h) : ℕ) : K) = 1 := by
    simpa [Nat.cast_add, Nat.cast_mul, mul_assoc] using hmulK
  have hnat : m * ((alpha1 + alpha2) * h) = 1 := by
    exact_mod_cast hcast
  have hm1 : 1 ≤ m := Nat.succ_le_iff.mpr hm
  have hh1 : 1 ≤ h := Nat.succ_le_iff.mpr hh
  have hAhNat : 2 ≤ (alpha1 + alpha2) * h := by
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ (alpha1 + alpha2) * h := Nat.mul_le_mul hA0nat hh1
  have hprod : 2 ≤ m * ((alpha1 + alpha2) * h) := by
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ m * ((alpha1 + alpha2) * h) := Nat.mul_le_mul hm1 hAhNat
  omega

end

end HC4.Polynomial
