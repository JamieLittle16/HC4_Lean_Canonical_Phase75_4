import HC4.RationalRigidity.LogarithmicInfinityCertificate
import HC4.Polynomial.RankThreeFractionBridge
import Mathlib.Tactic

/-!
# A18.5.8: automatic nondegeneracy at an honest rank-three endpoint

The mature rank-three infinity assembly asks for two scalar side conditions in
addition to the fraction-core determinant equation:

* the raw autonomous target denominator is a nonzero polynomial;
* the canonical reduced denominator of `E(phi) / phi` has positive degree.

For the honest exponent line used in the HC4 terminal splice these conditions
are not extra hypotheses.

At the rank-three endpoint `rho = 0`, with

    v = (0,A,B,C),  A,B,C > 0,
    w = (P,Q,R,S),  P > 0,

the raw target denominator evaluates to

    (1 - A - B - C) * P^2 * A * B * C,

which is nonzero in characteristic zero.  The transverse direction entries
`Q,R,S` disappear completely.

For the logarithmic source, if `phi` has positive degree and nonzero constant
coefficient, then `E(phi)/phi` cannot reduce to a polynomial.  Indeed, a
constant reduced denominator would be the monic polynomial `1`; the canonical
cross identity would then make `phi` divide `E(phi)`.  Degree comparison forces
the quotient to be constant, while the constant coefficient of `E(phi)` is
zero and that of `phi` is nonzero, a contradiction.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- The raw rank-three autonomous denominator is automatically nonzero for an
honest rank-three endpoint and a direction genuinely leaving the omitted
coordinate. -/
theorem rankThreeEtaDenominatorPolynomial_ne_zero_of_positive_endpoint
    {A B C P : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (Q R S : K) :
    HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      (A : K) (B : K) (C : K) (P : K) Q R S ≠ 0 := by
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hP0 : (P : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hsum : (1 : K) - (A : K) - (B : K) - (C : K) ≠ 0 := by
    intro hzero
    have heq : (A : K) + (B : K) + (C : K) = 1 := by
      linear_combination -hzero
    have heqNat : A + B + C = 1 := by
      exact_mod_cast heq
    omega
  intro hpoly
  have heval :
      Polynomial.eval 0
        (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          (A : K) (B : K) (C : K) (P : K) Q R S) = 0 := by
    rw [hpoly]
    simp
  rw [HC4.Polynomial.eval_rankThreeEtaDenominatorPolynomial] at heval
  have hexp :
      HC4.Polynomial.rankThreeEtaDenominator
          (A : K) (B : K) (C : K) (P : K) Q R S 0 =
        ((1 : K) - (A : K) - (B : K) - (C : K)) *
          (P : K)^2 * (A : K) * (B : K) * (C : K) := by
    simp [HC4.Polynomial.rankThreeEtaDenominator,
      HC4.Polynomial.rankThreeLogSum,
      HC4.Polynomial.rankThreeWeightedCofactorSum,
      HC4.Polynomial.rankThreeDirectionDefect,
      HC4.Polynomial.rankThreeLogProduct]
    ring
  rw [hexp] at heval
  exact (mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hsum (pow_ne_zero 2 hP0)) hA0) hB0) hC0) heval

/-- A positive-degree polynomial with nonzero constant coefficient has a
nonconstant reduced logarithmic-source denominator. -/
theorem logarithmicSourceDenominator_natDegree_pos_of_coeff_zero_ne_zero
    (phi : Polynomial K)
    (hdeg : 0 < phi.natDegree)
    (hconst : phi.coeff 0 ≠ 0) :
    0 < (logarithmicSourceDenominator phi).natDegree := by
  let D := logarithmicSourceDenominator phi
  let N := logarithmicSourceNumerator phi
  have hphi : phi ≠ 0 := by
    intro hzero
    subst phi
    simp at hconst
  have hEdeg :
      (HC4.Polynomial.eulerDerivative phi).natDegree = phi.natDegree :=
    natDegree_eulerDerivative_eq_of_pos phi hdeg
  have hE : HC4.Polynomial.eulerDerivative phi ≠ 0 := by
    intro hzero
    have hz : (HC4.Polynomial.eulerDerivative phi).natDegree = 0 := by
      rw [hzero]
      simp
    rw [hEdeg] at hz
    omega
  by_contra hnot
  have hDdeg : D.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hDne : D ≠ 0 := by
    simpa [D] using logarithmicSource_denominator_ne_zero phi
  have hDmonic : D.Monic := by
    simpa [D] using logarithmicSource_denominator_monic phi
  have hDcoeff : D.coeff 0 = 1 := by
    change D.leadingCoeff = 1 at hDmonic
    change D.coeff D.natDegree = 1 at hDmonic
    simpa [hDdeg] using hDmonic
  have hDone : D = 1 := by
    calc
      D = Polynomial.C (D.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hDdeg
      _ = 1 := by simp [hDcoeff]
  have hcross : N * phi = HC4.Polynomial.eulerDerivative phi := by
    have h := logarithmicSource_cross_identity phi hphi
    simpa [N, D, hDone] using h
  have hN : N ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hcross
    exact hE hcross.symm
  have hdegCross := congrArg Polynomial.natDegree hcross
  rw [Polynomial.natDegree_mul hN hphi, hEdeg] at hdegCross
  have hNdeg : N.natDegree = 0 := by omega
  have hNC : N = Polynomial.C (N.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hNdeg
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 0) hcross
  have hNconst : N.coeff 0 = 0 := by
    rw [hNC] at hcoeff
    simp [HC4.Polynomial.coeff_eulerDerivative] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_right hconst
  apply hN
  rw [hNC, hNconst]
  simp

end

end HC4.RationalRigidity
