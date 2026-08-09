import HC4.Polynomial.LogarithmicInitialSlope
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# Quadratic rigidity for the autonomous logarithmic ODE

This file formalises the coefficient-theoretic part of manuscript Lemma 4.1.
Write

    E(phi) = X phi',
    rho = E(phi) / phi,
    eta = X rho'.

After clearing `phi^2`, an autonomous quadratic equation

    eta = A rho^2 + B rho

is exactly

    logarithmicEtaNumerator phi
      = C A * E(phi)^2 + C B * (phi * E(phi)).

For a polynomial with nonzero constant term and least positive exponent `m`,
the coefficient of degree `m` forces `B = m`.  Comparing the top possible
coefficient, in degree `2 * natDegree phi`, forces

    A * natDegree(phi) + B = 0.

These two identities are the only global coefficient information used in the
rank-three proof once the autonomous rational right-hand side is known to be
quadratic.
-/

namespace HC4.Polynomial

noncomputable section

/-- Denominator-cleared form of `eta = A rho^2 + B rho`. -/
def QuadraticAutonomousLogODE
    {K : Type*} [CommRing K]
    (A B : K) (phi : Polynomial K) : Prop :=
  logarithmicEtaNumerator phi =
    Polynomial.C A * (eulerDerivative phi)^2 +
      Polynomial.C B * logarithmicEtaOverRhoDenominator phi

/-- Euler differentiation does not increase natural degree. -/
theorem natDegree_eulerDerivative_le
    {K : Type*} [CommSemiring K]
    (p : Polynomial K) :
    (eulerDerivative p).natDegree ≤ p.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_eulerDerivative]
  have hp : p.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [hp]

/-- Two Euler differentiations still do not increase natural degree. -/
theorem natDegree_eulerDerivative_eulerDerivative_le
    {K : Type*} [CommSemiring K]
    (p : Polynomial K) :
    (eulerDerivative (eulerDerivative p)).natDegree ≤ p.natDegree := by
  exact le_trans (natDegree_eulerDerivative_le (eulerDerivative p))
    (natDegree_eulerDerivative_le p)

/-- The coefficient of the quadratic Euler term at the least positive exponent
vanishes: `E(phi)` is already divisible by `X^m`, so its square starts in
exponent `2m`. -/
theorem coeff_m_sq_eulerDerivative_local_form
    {K : Type*} [CommRing K]
    (c : K) (q : Polynomial K) {m : ℕ} (hm : 0 < m) :
    ((eulerDerivative
      (Polynomial.C c + Polynomial.X ^ m * q))^2).coeff m = 0 := by
  rw [eulerDerivative_local_form]
  let g : Polynomial K := Polynomial.C (m : K) * q + eulerDerivative q
  change ((Polynomial.X ^ m * g)^2).coeff m = 0
  rw [show
      (Polynomial.X ^ m * g)^2 =
        Polynomial.X ^ (m + m) * g^2 by
      rw [pow_two, pow_add]
      ring]
  rw [Polynomial.coeff_X_pow_mul']
  have hlt : m < m + m := by omega
  simp [Nat.not_le.mpr hlt]

/-- The least positive coefficient of a quadratic autonomous equation forces
its linear coefficient to be the least positive exponent. -/
theorem quadraticAutonomous_linearCoefficient_eq
    {K : Type*} [Field K] [CharZero K]
    {A B c : K} {q : Polynomial K} {m : ℕ}
    (hm : 0 < m) (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hode : QuadraticAutonomousLogODE A B
      (Polynomial.C c + Polynomial.X ^ m * q)) :
    B = (m : K) := by
  have hcoeff := congrArg
    (fun p : Polynomial K => p.coeff m) hode
  unfold QuadraticAutonomousLogODE at hcoeff
  change
    (logarithmicEtaNumerator
      (Polynomial.C c + Polynomial.X ^ m * q)).coeff m =
      (Polynomial.C A *
          (eulerDerivative
            (Polynomial.C c + Polynomial.X ^ m * q))^2 +
        Polynomial.C B *
          logarithmicEtaOverRhoDenominator
            (Polynomial.C c + Polynomial.X ^ m * q)).coeff m at hcoeff
  rw [coeff_m_logarithmicEtaNumerator_local_form c q hm] at hcoeff
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul] at hcoeff
  rw [coeff_m_sq_eulerDerivative_local_form c q hm] at hcoeff
  rw [coeff_m_logarithmicEtaOverRhoDenominator_local_form c q hm] at hcoeff
  simp only [mul_zero, zero_add] at hcoeff

  have hmK : (m : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hpref : (m : K) * q.coeff 0 * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero hmK hq0) hc
  have hprod :
      ((m : K) - B) * ((m : K) * q.coeff 0 * c) = 0 := by
    calc
      ((m : K) - B) * ((m : K) * q.coeff 0 * c) =
          (m : K)^2 * q.coeff 0 * c -
            B * (c * (m : K) * q.coeff 0) := by ring
      _ = 0 := by linear_combination hcoeff
  have hsub : (m : K) - B = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hpref
  exact (sub_eq_zero.mp hsub).symm

/-- Top-degree coefficient relation for a quadratic autonomous logarithmic
ODE.  If `D = natDegree phi > 0`, then `A*D + B = 0`. -/
theorem quadraticAutonomous_top_relation
    {K : Type*} [Field K] [CharZero K]
    {A B : K} {phi : Polynomial K}
    (hD : 0 < phi.natDegree)
    (hode : QuadraticAutonomousLogODE A B phi) :
    A * (phi.natDegree : K) + B = 0 := by
  let D : ℕ := phi.natDegree
  have hphi : phi ≠ 0 := by
    intro hz
    rw [hz] at hD
    simp at hD
  have htop : phi.coeff D ≠ 0 := by
    change phi.leadingCoeff ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).2 hphi
  have hDK : (D : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)

  have hE_le : (eulerDerivative phi).natDegree ≤ D := by
    exact natDegree_eulerDerivative_le phi
  have hEE_le :
      (eulerDerivative (eulerDerivative phi)).natDegree ≤ D := by
    exact natDegree_eulerDerivative_eulerDerivative_le phi

  have hEcoeff :
      (eulerDerivative phi).coeff D = (D : K) * phi.coeff D := by
    rw [coeff_eulerDerivative]
  have hEtop : (eulerDerivative phi).coeff D ≠ 0 := by
    rw [hEcoeff]
    exact mul_ne_zero hDK htop
  have hEdeg : (eulerDerivative phi).natDegree = D := by
    apply le_antisymm hE_le
    by_contra hnot
    have hlt : (eulerDerivative phi).natDegree < D := Nat.lt_of_not_ge hnot
    exact hEtop (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)

  have hEEcoeff :
      (eulerDerivative (eulerDerivative phi)).coeff D =
        (D : K) * (eulerDerivative phi).coeff D := by
    rw [coeff_eulerDerivative]
  have hEEtop :
      (eulerDerivative (eulerDerivative phi)).coeff D ≠ 0 := by
    rw [hEEcoeff]
    exact mul_ne_zero hDK hEtop
  have hEEdeg :
      (eulerDerivative (eulerDerivative phi)).natDegree = D := by
    apply le_antisymm hEE_le
    by_contra hnot
    have hlt :
        (eulerDerivative (eulerDerivative phi)).natDegree < D :=
      Nat.lt_of_not_ge hnot
    exact hEEtop (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)

  have hEEphi :
      (eulerDerivative (eulerDerivative phi) * phi).coeff (D + D) =
        (eulerDerivative (eulerDerivative phi)).coeff D * phi.coeff D := by
    have h := Polynomial.coeff_mul_degree_add_degree
      (eulerDerivative (eulerDerivative phi)) phi
    change
      (eulerDerivative (eulerDerivative phi) * phi).coeff
          ((eulerDerivative (eulerDerivative phi)).natDegree + phi.natDegree) =
        (eulerDerivative (eulerDerivative phi)).coeff
            (eulerDerivative (eulerDerivative phi)).natDegree *
          phi.coeff phi.natDegree at h
    rw [hEEdeg] at h
    simpa [D] using h
  have hEsq :
      ((eulerDerivative phi)^2).coeff (D + D) =
        (eulerDerivative phi).coeff D * (eulerDerivative phi).coeff D := by
    rw [pow_two]
    have h := Polynomial.coeff_mul_degree_add_degree
      (eulerDerivative phi) (eulerDerivative phi)
    change
      (eulerDerivative phi * eulerDerivative phi).coeff
          ((eulerDerivative phi).natDegree +
            (eulerDerivative phi).natDegree) =
        (eulerDerivative phi).coeff (eulerDerivative phi).natDegree *
          (eulerDerivative phi).coeff (eulerDerivative phi).natDegree at h
    rw [hEdeg] at h
    exact h
  have hphiE :
      (logarithmicEtaOverRhoDenominator phi).coeff (D + D) =
        phi.coeff D * (eulerDerivative phi).coeff D := by
    unfold logarithmicEtaOverRhoDenominator
    have h := Polynomial.coeff_mul_degree_add_degree
      phi (eulerDerivative phi)
    change
      (phi * eulerDerivative phi).coeff
          (phi.natDegree + (eulerDerivative phi).natDegree) =
        phi.coeff phi.natDegree *
          (eulerDerivative phi).coeff (eulerDerivative phi).natDegree at h
    rw [hEdeg] at h
    simpa [D] using h

  have hNtop : (logarithmicEtaNumerator phi).coeff (D + D) = 0 := by
    unfold logarithmicEtaNumerator
    rw [Polynomial.coeff_sub, hEEphi, hEsq, hEEcoeff, hEcoeff]
    ring

  have hcoeff := congrArg
    (fun p : Polynomial K => p.coeff (D + D)) hode
  unfold QuadraticAutonomousLogODE at hcoeff
  change
    (logarithmicEtaNumerator phi).coeff (D + D) =
      (Polynomial.C A * (eulerDerivative phi)^2 +
        Polynomial.C B * logarithmicEtaOverRhoDenominator phi).coeff
          (D + D) at hcoeff
  rw [hNtop, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    hEsq, hphiE, hEcoeff] at hcoeff

  have hprefix : (D : K) * (phi.coeff D)^2 ≠ 0 :=
    mul_ne_zero hDK (pow_ne_zero 2 htop)
  have hprod :
      ((D : K) * (phi.coeff D)^2) *
        (A * (D : K) + B) = 0 := by
    calc
      ((D : K) * (phi.coeff D)^2) *
          (A * (D : K) + B) =
        A * (((D : K) * phi.coeff D) *
          ((D : K) * phi.coeff D)) +
        B * (phi.coeff D * ((D : K) * phi.coeff D)) := by ring
      _ = 0 := by linear_combination -hcoeff
  exact (mul_eq_zero.mp hprod).resolve_left hprefix

/-- For a local polynomial, the two coefficient constraints combine to
`A * D + m = 0`. -/
theorem quadraticAutonomous_local_top_relation
    {K : Type*} [Field K] [CharZero K]
    {A B c : K} {q : Polynomial K} {m : ℕ}
    (hm : 0 < m) (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hode : QuadraticAutonomousLogODE A B
      (Polynomial.C c + Polynomial.X ^ m * q)) :
    A * ((Polynomial.C c + Polynomial.X ^ m * q).natDegree : K) +
      (m : K) = 0 := by
  have hq : q ≠ 0 := by
    intro hqz
    apply hq0
    simp [hqz]
  have hdeg :
      0 < (Polynomial.C c + Polynomial.X ^ m * q).natDegree := by
    rw [Polynomial.natDegree_C_add]
    rw [Polynomial.natDegree_X_pow_mul m hq]
    omega
  have hB := quadraticAutonomous_linearCoefficient_eq
    (A := A) (B := B) hm hc hq0 hode
  have htop := quadraticAutonomous_top_relation
    (A := A) (B := B) hdeg hode
  rw [hB] at htop
  exact htop

/-- The rank-three `J = empty` quadratic coefficient `A = -1` forces the
polynomial to have only its constant term and its first positive term. -/
theorem eq_two_term_of_quadraticAutonomous_leading_neg_one
    {K : Type*} [Field K] [CharZero K]
    {B c : K} {q : Polynomial K} {m : ℕ}
    (hm : 0 < m) (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hode : QuadraticAutonomousLogODE (-1 : K) B
      (Polynomial.C c + Polynomial.X ^ m * q)) :
    Polynomial.C c + Polynomial.X ^ m * q =
      Polynomial.C c + Polynomial.C (q.coeff 0) * Polynomial.X ^ m := by
  have hrel := quadraticAutonomous_local_top_relation
    (A := (-1 : K)) (B := B) hm hc hq0 hode
  have hmd :
      (m : K) -
        ((Polynomial.C c + Polynomial.X ^ m * q).natDegree : K) = 0 := by
    simpa [sub_eq_add_neg, add_comm] using hrel
  have hdegCast :
      (((Polynomial.C c + Polynomial.X ^ m * q).natDegree : ℕ) : K) =
        (m : K) := by
    exact (sub_eq_zero.mp hmd).symm
  have hdeg :
      (Polynomial.C c + Polynomial.X ^ m * q).natDegree = m := by
    exact_mod_cast hdegCast

  have hq : q ≠ 0 := by
    intro hqz
    apply hq0
    simp [hqz]
  have hdegq : q.natDegree = 0 := by
    have hdeg' := hdeg
    rw [Polynomial.natDegree_C_add,
      Polynomial.natDegree_X_pow_mul m hq] at hdeg'
    omega
  have hqC : q = Polynomial.C (q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdegq
  have hmul :
      Polynomial.X ^ m * q =
        Polynomial.X ^ m * Polynomial.C (q.coeff 0) :=
    congrArg (fun p : Polynomial K => Polynomial.X ^ m * p) hqC
  calc
    Polynomial.C c + Polynomial.X ^ m * q =
        Polynomial.C c + Polynomial.X ^ m * Polynomial.C (q.coeff 0) :=
      congrArg (fun p : Polynomial K => Polynomial.C c + p) hmul
    _ = Polynomial.C c + Polynomial.C (q.coeff 0) * Polynomial.X ^ m := by
      rw [mul_comm (Polynomial.X ^ m) (Polynomial.C (q.coeff 0))]

/-- A positive reciprocal quadratic coefficient, of the form occurring in the
rank-three `J != empty`, `M_J >= 2` asymptotic, is incompatible with a
nonconstant polynomial solution. -/
theorem no_quadraticAutonomous_positive_reciprocal
    {K : Type*} [Field K] [CharZero K]
    {B c : K} {q : Polynomial K} {m J : ℕ}
    (hm : 0 < m) (hJ : 2 ≤ J)
    (hc : c ≠ 0) (hq0 : q.coeff 0 ≠ 0)
    (hode : QuadraticAutonomousLogODE
      (1 / (((J : K) - 1))) B
      (Polynomial.C c + Polynomial.X ^ m * q)) : False := by
  have hrel := quadraticAutonomous_local_top_relation
    (A := (1 / (((J : K) - 1)))) (B := B)
    hm hc hq0 hode
  let D : ℕ := (Polynomial.C c + Polynomial.X ^ m * q).natDegree
  have hJsubNat : 0 < J - 1 := by omega
  have hJne1 : J ≠ 1 := by omega
  have hJcastNe1 : (J : K) ≠ 1 := by
    exact_mod_cast hJne1
  have hJsubK : (J : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr hJcastNe1
  have hcleared :
      (D : K) + (m : K) * ((J : K) - 1) = 0 := by
    dsimp [D] at hrel ⊢
    field_simp [hJsubK] at hrel
    linear_combination hrel
  have h1J : 1 ≤ J := by omega
  have hcastJ : ((J - 1 : ℕ) : K) = (J : K) - 1 := by
    have hcastJ' :
        ((J - 1 : ℕ) : K) = (J : K) - ((1 : ℕ) : K) :=
      (Nat.cast_sub h1J :
        ((J - 1 : ℕ) : K) = (J : K) - ((1 : ℕ) : K))
    simpa using hcastJ'
  have hcastZero :
      ((D + m * (J - 1) : ℕ) : K) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hcastJ]
    exact hcleared
  have hpositive : 0 < D + m * (J - 1) := by
    have : 0 < m * (J - 1) := Nat.mul_pos hm hJsubNat
    omega
  have hnonzero : ((D + m * (J - 1) : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpositive)
  exact hnonzero hcastZero

end

end HC4.Polynomial
