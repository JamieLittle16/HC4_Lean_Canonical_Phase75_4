import HC4.Polynomial.AutonomousODEPoleOrder
import Mathlib.Tactic

/-!
# Polynomial degree bound for autonomous logarithmic ODEs

This file turns the local pole-order certificate from Phase 78 into the
finite coefficient contradiction used in the symmetric-gradings manuscript.

After translating a genuine nonzero root to `X = 0`, write

    phi = X^(n+1) q,   q(0) != 0,
    E   = shiftedEuler alpha phi,
    N   = shiftedEtaNumerator alpha phi.

For a polynomial autonomous right-hand side `R` of degree `d`, clearing the
powers of `phi` gives

    N * phi^(d-2)
      = sum_j C(r_j) * E^j * phi^(d-j).

The left side starts in degree

    2n + (n+1)(d-2) = nd + d - 2,

whereas the leading `j=d` term on the right starts in degree `nd` with a
nonzero coefficient.  Every lower `j<d` term starts strictly after `nd`.
Thus `d >= 3` is impossible.

This is the coefficient-theoretic replacement for the manuscript statement
that the pole order forces the autonomous polynomial `R` to be quadratic.
-/

namespace HC4.Polynomial

noncomputable section

/-- Powers preserve an explicit `X`-power factor. -/
theorem X_pow_mul_pow
    {K : Type*} [CommRing K]
    (a d : ℕ) (p : Polynomial K) :
    (Polynomial.X ^ a * p) ^ d =
      Polynomial.X ^ (a * d) * p ^ d := by
  rw [mul_pow]
  rw [pow_mul]

/-- Constant coefficients commute with the two explicit `X`-power factors. -/
theorem C_mul_X_pow_mul_mul_X_pow_mul
    {K : Type*} [CommRing K]
    (c : K) (a b : ℕ) (p q : Polynomial K) :
    (Polynomial.C c * (Polynomial.X ^ a * p)) *
        (Polynomial.X ^ b * q) =
      Polynomial.X ^ (a + b) * (Polynomial.C c * p * q) := by
  calc
    (Polynomial.C c * (Polynomial.X ^ a * p)) *
        (Polynomial.X ^ b * q) =
      Polynomial.C c *
        ((Polynomial.X ^ a * p) * (Polynomial.X ^ b * q)) := by ring
    _ = Polynomial.C c *
        (Polynomial.X ^ (a + b) * (p * q)) := by
      rw [X_pow_mul_mul_X_pow_mul]
    _ = Polynomial.X ^ (a + b) * (Polynomial.C c * p * q) := by ring

/-- The constant coefficient of a power is the corresponding power of the
constant coefficient. -/
theorem coeff_zero_pow
    {K : Type*} [CommSemiring K]
    (p : Polynomial K) (d : ℕ) :
    (p ^ d).coeff 0 = (p.coeff 0) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, pow_succ, Polynomial.mul_coeff_zero, ih]

/-- The shifted eta numerator has an exact `X^(2n)` factor at a root of
multiplicity `n+1`. -/
theorem exists_shiftedEtaNumerator_factor
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n : ℕ) :
    ∃ H : Polynomial K,
      shiftedEtaNumerator alpha (Polynomial.X ^ (n + 1) * q) =
        Polynomial.X ^ (n + n) * H := by
  cases n with
  | zero =>
      refine ⟨shiftedEtaNumerator alpha (Polynomial.X ^ (0 + 1) * q), ?_⟩
      simp
  | succ k =>
      let g : Polynomial K := shiftedEulerCore alpha (k + 2) q
      let h : Polynomial K := shiftedEulerCore alpha (k + 1) g
      have hE :
          shiftedEuler alpha (Polynomial.X ^ (k + 2) * q) =
            Polynomial.X ^ (k + 1) * g := by
        simpa [g, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          shiftedEuler_X_pow_succ_mul (K := K) alpha q (k + 1)
      have hEE :
          shiftedEuler alpha (Polynomial.X ^ (k + 1) * g) =
            Polynomial.X ^ k * h := by
        simpa [h] using
          shiftedEuler_X_pow_succ_mul (K := K) alpha g k
      refine ⟨h * q - g ^ 2, ?_⟩
      unfold shiftedEtaNumerator
      rw [hE, hEE]
      have hsum : k + (k + 2) = (k + 1) + (k + 1) := by omega
      rw [X_pow_mul_mul_X_pow_mul, hsum]
      rw [pow_two, X_pow_mul_mul_X_pow_mul]
      ring

/-- Multiplying the shifted eta numerator by an additional power of `phi`
retains the exact lower `X`-power factor predicted by root order. -/
theorem exists_shiftedEta_mul_phi_pow_factor
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n e : ℕ) :
    ∃ H : Polynomial K,
      shiftedEtaNumerator alpha (Polynomial.X ^ (n + 1) * q) *
          (Polynomial.X ^ (n + 1) * q) ^ e =
        Polynomial.X ^ ((n + n) + (n + 1) * e) * H := by
  obtain ⟨H, hH⟩ := exists_shiftedEtaNumerator_factor
    (K := K) alpha q n
  refine ⟨H * q ^ e, ?_⟩
  rw [hH, X_pow_mul_pow]
  exact X_pow_mul_mul_X_pow_mul (n + n) ((n + 1) * e) H (q ^ e)

/-- If at least one extra `phi` factor is present, the coefficient in the
would-be leading autonomous degree vanishes on the eta side. -/
theorem coeff_n_mul_e_add_two_shiftedEta_mul_phi_pow_zero
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n e : ℕ) (he : 0 < e) :
    (shiftedEtaNumerator alpha (Polynomial.X ^ (n + 1) * q) *
      (Polynomial.X ^ (n + 1) * q) ^ e).coeff (n * (e + 2)) = 0 := by
  obtain ⟨H, hH⟩ := exists_shiftedEta_mul_phi_pow_factor
    (K := K) alpha q n e
  rw [hH, Polynomial.coeff_X_pow_mul']
  have hexp :
      (n + n) + (n + 1) * e = n * (e + 2) + e := by ring
  have hlt : n * (e + 2) < (n + n) + (n + 1) * e := by
    rw [hexp]
    exact Nat.lt_add_of_pos_right he
  simp [Nat.not_le.mpr hlt]

/-- Exact coefficient of a power of the shifted Euler numerator at its first
possible degree. -/
theorem coeff_n_mul_d_shiftedEuler_pow
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n d : ℕ) :
    ((shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)) ^ d).coeff
        (n * d) =
      (alpha * ((n + 1 : ℕ) : K) * q.coeff 0) ^ d := by
  rw [shiftedEuler_X_pow_succ_mul]
  rw [X_pow_mul_pow]
  rw [Polynomial.coeff_X_pow_mul']
  simp only [le_refl, if_true, Nat.sub_self]
  rw [coeff_zero_pow, coeff_zero_shiftedEulerCore]

/-- A lower homogenised autonomous term starts strictly after degree
`n*(j+e)` whenever it contains at least one `phi` factor. -/
theorem coeff_n_mul_j_add_e_shiftedEuler_pow_mul_phi_pow_zero
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n j e : ℕ) (he : 0 < e) :
    ((shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)) ^ j *
      (Polynomial.X ^ (n + 1) * q) ^ e).coeff (n * (j + e)) = 0 := by
  rw [shiftedEuler_X_pow_succ_mul]
  rw [X_pow_mul_pow, X_pow_mul_pow]
  rw [X_pow_mul_mul_X_pow_mul]
  rw [Polynomial.coeff_X_pow_mul']
  have hexp :
      n * j + (n + 1) * e = n * (j + e) + e := by ring
  have hlt : n * (j + e) < n * j + (n + 1) * e := by
    rw [hexp]
    exact Nat.lt_add_of_pos_right he
  simp [Nat.not_le.mpr hlt]

/-- Homogenised numerator obtained by clearing the powers of `phi` in a
polynomial autonomous equation `eta = R(rho)`. -/
def shiftedAutonomousClearedRHS
    {K : Type*} [CommRing K]
    (alpha : K) (R phi : Polynomial K) : Polynomial K :=
  let d := R.natDegree
  R.sum fun j a =>
    Polynomial.C a * (shiftedEuler alpha phi) ^ j * phi ^ (d - j)

/-- Denominator-cleared polynomial autonomous equation after translating a
root to the origin.  It is intended for `natDegree R >= 2`. -/
def ShiftedPolynomialAutonomousLogODE
    {K : Type*} [CommRing K]
    (alpha : K) (R phi : Polynomial K) : Prop :=
  shiftedEtaNumerator alpha phi * phi ^ (R.natDegree - 2) =
    shiftedAutonomousClearedRHS alpha R phi

/-- At the pole-order coefficient `n * deg R`, only the leading term of the
homogenised autonomous polynomial survives. -/
theorem coeff_n_mul_natDegree_shiftedAutonomousClearedRHS
    {K : Type*} [Field K]
    {alpha : K} {R q : Polynomial K} {n : ℕ}
    (hR : R ≠ 0) :
    (shiftedAutonomousClearedRHS alpha R
      (Polynomial.X ^ (n + 1) * q)).coeff (n * R.natDegree) =
      R.leadingCoeff *
        (alpha * ((n + 1 : ℕ) : K) * q.coeff 0) ^ R.natDegree := by
  classical
  let d : ℕ := R.natDegree
  have hdmem : d ∈ R.support := by
    rw [Polynomial.mem_support_iff]
    change R.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hR
  unfold shiftedAutonomousClearedRHS
  dsimp only
  rw [Polynomial.sum_def, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single d]
  · change
      (Polynomial.C (R.coeff d) *
        (shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)) ^ d *
        (Polynomial.X ^ (n + 1) * q) ^ (d - d)).coeff (n * d) =
      R.leadingCoeff *
        (alpha * ((n + 1 : ℕ) : K) * q.coeff 0) ^ d
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [Polynomial.coeff_C_mul]
    rw [coeff_n_mul_d_shiftedEuler_pow]
    rfl
  · intro j hj hjd
    have hjle : j ≤ d := Polynomial.le_natDegree_of_mem_supp j hj
    have hjlt : j < d := lt_of_le_of_ne hjle hjd
    let e : ℕ := d - j
    have he : 0 < e := by
      dsimp [e]
      exact Nat.sub_pos_of_lt hjlt
    have hsum : j + e = d := by
      dsimp [e]
      omega
    have hzero :=
      coeff_n_mul_j_add_e_shiftedEuler_pow_mul_phi_pow_zero
        (K := K) alpha q n j e he
    rw [hsum] at hzero
    change
      (Polynomial.C (R.coeff j) *
        (shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)) ^ j *
        (Polynomial.X ^ (n + 1) * q) ^ e).coeff (n * d) = 0
    rw [mul_assoc, Polynomial.coeff_C_mul, hzero, mul_zero]
  · intro hnot
    exact (hnot hdmem).elim

/-- A polynomial autonomous right-hand side cannot have degree at least
three at a genuine nonzero root. -/
theorem no_shiftedPolynomialAutonomousLogODE_degree_ge_three
    {K : Type*} [Field K] [CharZero K]
    {alpha : K} {R q : Polynomial K} {n : ℕ}
    (halpha : alpha ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hdeg : 3 ≤ R.natDegree)
    (hode : ShiftedPolynomialAutonomousLogODE alpha R
      (Polynomial.X ^ (n + 1) * q)) : False := by
  let d : ℕ := R.natDegree
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have he : 0 < d - 2 := by
    dsimp [d]
    omega
  have hdform : d - 2 + 2 = d := by
    dsimp [d]
    omega
  have hleft0 :
      (shiftedEtaNumerator alpha (Polynomial.X ^ (n + 1) * q) *
        (Polynomial.X ^ (n + 1) * q) ^ (d - 2)).coeff (n * d) = 0 := by
    have h := coeff_n_mul_e_add_two_shiftedEta_mul_phi_pow_zero
      (K := K) alpha q n (d - 2) he
    rw [hdform] at h
    exact h
  have hright := coeff_n_mul_natDegree_shiftedAutonomousClearedRHS
    (K := K) (alpha := alpha) (R := R) (q := q) (n := n) hR
  change
    (shiftedAutonomousClearedRHS alpha R
      (Polynomial.X ^ (n + 1) * q)).coeff (n * d) =
      R.leadingCoeff *
        (alpha * ((n + 1 : ℕ) : K) * q.coeff 0) ^ d at hright

  unfold ShiftedPolynomialAutonomousLogODE at hode
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff (n * d)) hode
  change
    (shiftedEtaNumerator alpha (Polynomial.X ^ (n + 1) * q) *
      (Polynomial.X ^ (n + 1) * q) ^ (d - 2)).coeff (n * d) =
    (shiftedAutonomousClearedRHS alpha R
      (Polynomial.X ^ (n + 1) * q)).coeff (n * d) at hcoeff
  rw [hleft0, hright] at hcoeff

  have hM : (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hbase : alpha * ((n + 1 : ℕ) : K) * q.coeff 0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero halpha hM) hq0
  have hlead : R.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hR
  have hrightne :
      R.leadingCoeff *
        (alpha * ((n + 1 : ℕ) : K) * q.coeff 0) ^ d ≠ 0 :=
    mul_ne_zero hlead (pow_ne_zero d hbase)
  exact hrightne hcoeff.symm

/-- Consequently, any polynomial autonomous right-hand side satisfying the
translated logarithmic ODE at a genuine nonzero root has degree at most two. -/
theorem natDegree_le_two_of_shiftedPolynomialAutonomousLogODE
    {K : Type*} [Field K] [CharZero K]
    {alpha : K} {R q : Polynomial K} {n : ℕ}
    (halpha : alpha ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hode : ShiftedPolynomialAutonomousLogODE alpha R
      (Polynomial.X ^ (n + 1) * q)) :
    R.natDegree ≤ 2 := by
  by_contra hnot
  have hdeg : 3 ≤ R.natDegree := by omega
  exact no_shiftedPolynomialAutonomousLogODE_degree_ge_three
    halpha hq0 hdeg hode

end

end HC4.Polynomial
