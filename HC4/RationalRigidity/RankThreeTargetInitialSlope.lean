import HC4.RationalRigidity.RankThreeInfinityAssembly
import HC4.RationalRigidity.RankThreeEndpointNondegeneracy
import Mathlib.Tactic

/-!
# A18.5.27: initial slope of the rank-three autonomous target

Once the reduced target denominator is constant, the canonical polynomial
autonomous target represents the same rational function as the raw rank-three
numerator/denominator.  Their polynomial cross identity therefore determines
the first two coefficients of the autonomous polynomial at `rho=0`.

For a genuine rank-three endpoint `v=(0,A,B,C)` and a direction whose omitted
coordinate is `P`, direct expansion gives

    N_raw(0)  = 0,
    N_raw'(0) = P*A*B*C*(1-A-B-C),
    D_raw(0)  = P^2*A*B*C*(1-A-B-C).

When `A,B,C,P` are positive naturals, the last scalar is nonzero.  Hence the
polynomial target has constant coefficient zero and linear coefficient
`1/P`.  This is the precise scalar fact needed to compare the geometric edge
parameter with Phase 77's least-positive source exponent.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Raw rank-three numerator vanishes at the rank-three endpoint. -/
theorem eval_zero_rankThreeEtaNumeratorPolynomial
    (A B C P Q R S : K) :
    Polynomial.eval 0
      (HC4.Polynomial.rankThreeEtaNumeratorPolynomial A B C P Q R S) = 0 := by
  rw [HC4.Polynomial.eval_rankThreeEtaNumeratorPolynomial]
  simp [HC4.Polynomial.rankThreeEtaNumerator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum]

/-- First derivative of the raw numerator at the rank-three endpoint. -/
theorem eval_zero_derivative_rankThreeEtaNumeratorPolynomial
    (A B C P Q R S : K) :
    Polynomial.eval 0
      (Polynomial.derivative
        (HC4.Polynomial.rankThreeEtaNumeratorPolynomial A B C P Q R S)) =
      P * A * B * C * (1 - A - B - C) := by
  simp [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
    HC4.Polynomial.rankThreeEtaNumerator,
    HC4.Polynomial.rankThreeLogProduct,
    HC4.Polynomial.rankThreeLogSum,
    Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.derivative_sub]
  ring

/-- Constant value of the raw denominator at the rank-three endpoint. -/
theorem eval_zero_rankThreeEtaDenominatorPolynomial
    (A B C P Q R S : K) :
    Polynomial.eval 0
      (HC4.Polynomial.rankThreeEtaDenominatorPolynomial A B C P Q R S) =
      (1 - A - B - C) * P^2 * A * B * C := by
  rw [HC4.Polynomial.eval_rankThreeEtaDenominatorPolynomial]
  simp [HC4.Polynomial.rankThreeEtaDenominator,
    HC4.Polynomial.rankThreeLogSum,
    HC4.Polynomial.rankThreeWeightedCofactorSum,
    HC4.Polynomial.rankThreeDirectionDefect,
    HC4.Polynomial.rankThreeLogProduct]
  ring

/-- For positive natural endpoint data the raw denominator is already nonzero
at `rho=0`. -/
theorem eval_zero_rankThreeEtaDenominatorPolynomial_ne_zero_of_positive_endpoint
    {A B C P : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (Q R S : K) :
    Polynomial.eval 0
      (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S) ≠ 0 := by
  rw [eval_zero_rankThreeEtaDenominatorPolynomial]
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hP0 : (P : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hsum : (1 : K) - (A : K) - (B : K) - (C : K) ≠ 0 := by
    intro hzero
    have heq : (A : K) + (B : K) + (C : K) = 1 := by
      linear_combination -hzero
    have heqNat : A + B + C = 1 := by exact_mod_cast heq
    omega
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hsum (pow_ne_zero 2 hP0)) hA0) hB0) hC0

/-- Constant-denominator reduction gives the exact raw polynomial identity
`R * D_raw = N_raw`. -/
theorem rankThreeAutonomousPolynomial_mul_rawDenominator
    {A B C P : ℕ} {Q R S b : K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hb : b ≠ 0)
    (hden : rankThreeTargetDenominator
      (A : K) (B : K) (C : K) (P : K) Q R S = Polynomial.C b) :
    rankThreeAutonomousPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S b *
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S =
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S := by
  have hRawD :=
    rankThreeEtaDenominatorPolynomial_ne_zero_of_positive_endpoint
      (K := K) (A := A) (B := B) (C := C) (P := P)
      hA hB hC hP Q R S
  have hcross := rankThreeTarget_cross_identity
    (A : K) (B : K) (C : K) (P : K) Q R S hRawD
  unfold rankThreeAutonomousPolynomial
  calc
    (Polynomial.C b⁻¹ *
          rankThreeTargetNumerator
            (A : K) (B : K) (C : K) (P : K) Q R S) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          (A : K) (B : K) (C : K) (P : K) Q R S =
      Polynomial.C b⁻¹ *
        (rankThreeTargetNumerator
            (A : K) (B : K) (C : K) (P : K) Q R S *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (A : K) (B : K) (C : K) (P : K) Q R S) := by ring
    _ = Polynomial.C b⁻¹ *
        (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
            (A : K) (B : K) (C : K) (P : K) Q R S *
          rankThreeTargetDenominator
            (A : K) (B : K) (C : K) (P : K) Q R S) := by rw [hcross]
    _ = HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (P : K) Q R S := by
      rw [hden]
      simp [hb]

/-- **Initial coefficients of the polynomial rank-three target.** -/
theorem rankThreeAutonomousPolynomial_coeff_zero_one
    {A B C P : ℕ} {Q R S b : K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hb : b ≠ 0)
    (hden : rankThreeTargetDenominator
      (A : K) (B : K) (C : K) (P : K) Q R S = Polynomial.C b) :
    let T := rankThreeAutonomousPolynomial
      (A : K) (B : K) (C : K) (P : K) Q R S b
    T.coeff 0 = 0 ∧ T.coeff 1 = ((P : K)⁻¹) := by
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b
  let D := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S
  let N := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S
  have hraw : T * D = N := by
    simpa [T, D, N] using
      rankThreeAutonomousPolynomial_mul_rawDenominator
        hA hB hC hP hb hden
  have hD0 : Polynomial.eval 0 D ≠ 0 := by
    simpa [D] using
      eval_zero_rankThreeEtaDenominatorPolynomial_ne_zero_of_positive_endpoint
        (K := K) hA hB hC hP Q R S
  have hN0 : Polynomial.eval 0 N = 0 := by
    simpa [N] using
      eval_zero_rankThreeEtaNumeratorPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S
  have hT0eval : Polynomial.eval 0 T = 0 := by
    have h := congrArg (Polynomial.eval 0) hraw
    simp only [map_mul] at h
    rw [hN0] at h
    exact (mul_eq_zero.mp h).resolve_right hD0
  have hT0 : T.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hT0eval

  have hNder :
      Polynomial.eval 0 (Polynomial.derivative N) =
        (P : K) * (A : K) * (B : K) * (C : K) *
          (1 - (A : K) - (B : K) - (C : K)) := by
    simpa [N] using
      eval_zero_derivative_rankThreeEtaNumeratorPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S
  have hD0formula :
      Polynomial.eval 0 D =
        (1 - (A : K) - (B : K) - (C : K)) *
          (P : K)^2 * (A : K) * (B : K) * (C : K) := by
    simpa [D] using
      eval_zero_rankThreeEtaDenominatorPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S
  have hder := congrArg Polynomial.derivative hraw
  have hev := congrArg (Polynomial.eval 0) hder
  rw [Polynomial.derivative_mul] at hev
  simp only [map_add, map_mul] at hev
  rw [hT0eval, zero_mul, zero_add, hNder, hD0formula] at hev
  have hP0 : (P : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hsum : (1 : K) - (A : K) - (B : K) - (C : K) ≠ 0 := by
    intro hz
    have heq : (A : K) + (B : K) + (C : K) = 1 := by
      linear_combination -hz
    have heqNat : A + B + C = 1 := by exact_mod_cast heq
    omega
  have hfactor :
      (1 - (A : K) - (B : K) - (C : K)) *
          (P : K)^2 * (A : K) * (B : K) * (C : K) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero hsum (pow_ne_zero 2 hP0)) hA0) hB0) hC0
  have hderT : Polynomial.eval 0 (Polynomial.derivative T) = (P : K)⁻¹ := by
    apply (mul_right_cancel₀ hfactor)
    calc
      Polynomial.eval 0 (Polynomial.derivative T) *
          ((1 - (A : K) - (B : K) - (C : K)) *
            (P : K)^2 * (A : K) * (B : K) * (C : K)) =
        (P : K) * (A : K) * (B : K) * (C : K) *
          (1 - (A : K) - (B : K) - (C : K)) := hev
      _ = (P : K)⁻¹ *
          ((1 - (A : K) - (B : K) - (C : K)) *
            (P : K)^2 * (A : K) * (B : K) * (C : K)) := by
        field_simp [hP0]
        ring
  have hT1 : T.coeff 1 = (P : K)⁻¹ := by
    have hcoeff := congrArg (fun p : Polynomial K => p.coeff 0)
      (show Polynomial.derivative T = Polynomial.derivative T from rfl)
    rw [← Polynomial.coeff_zero_eq_eval_zero] at hderT
    simpa [Polynomial.coeff_derivative] using hderT
  exact ⟨hT0, hT1⟩

end

end HC4.RationalRigidity
