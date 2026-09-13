import HC4.RationalRigidity.RankThreeHomogeneousQFixedRelation
import Mathlib.Tactic

/-!
# A18.5.61: the remaining fixed-direction homogeneous relations

A18.5.60 opens the `Q = 0` branch of the homogeneous terminal one coefficient
further.  The two remaining branches are exactly symmetric at the level of the
raw autonomous target.

For `R = 0` the coefficient-three identity gives

    B * Q * (Q+1) * (A+B+C-1) * (A+C-D) = 0,

and for `S = 0` it gives

    C * Q * (Q+1) * (A+B+C-1) * (A+B-D) = 0,

where `D = natDegree phi`.

Together with A18.5.60 these three relations exhaust the fixed-transverse
alternative from A18.5.59.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 6000000 in
theorem coeff_one_rankThreeEtaDenominatorPolynomial_unit_of_homogeneous_R_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0)
    (hR : R = 0) :
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      A B C 1 Q R S).coeff 1 =
      -(B * Q * (Q + 1) * (A + C) * (A + B + C - 1)) := by
  have hS : S = -(1 + Q) := by
    rw [hR] at hsum
    linear_combination hsum
  rw [hR, hS]
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
      HC4.Polynomial.rankThreeEtaDenominator,
      HC4.Polynomial.rankThreeLogProduct,
      HC4.Polynomial.rankThreeLogSum,
      HC4.Polynomial.rankThreeWeightedCofactorSum,
      HC4.Polynomial.rankThreeDirectionDefect,
      Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_one, pow_two]
  ring

set_option maxHeartbeats 4000000 in
theorem coeff_three_rankThreeEtaNumeratorPolynomial_unit_of_homogeneous_R_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0)
    (hR : R = 0) :
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      A B C 1 Q R S).coeff 3 =
      B * Q * (Q + 1) * (A + B + C - 1) := by
  have hS : S = -(1 + Q) := by
    rw [hR] at hsum
    linear_combination hsum
  rw [hR, hS]
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
      HC4.Polynomial.rankThreeEtaNumerator,
      HC4.Polynomial.rankThreeLogProduct,
      HC4.Polynomial.rankThreeLogSum,
      Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_one, pow_two]
  ring

set_option maxHeartbeats 6000000 in
theorem coeff_one_rankThreeEtaDenominatorPolynomial_unit_of_homogeneous_S_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0)
    (hS : S = 0) :
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      A B C 1 Q R S).coeff 1 =
      -(C * Q * (Q + 1) * (A + B) * (A + B + C - 1)) := by
  have hR : R = -(1 + Q) := by
    rw [hS] at hsum
    linear_combination hsum
  rw [hS, hR]
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
      HC4.Polynomial.rankThreeEtaDenominator,
      HC4.Polynomial.rankThreeLogProduct,
      HC4.Polynomial.rankThreeLogSum,
      HC4.Polynomial.rankThreeWeightedCofactorSum,
      HC4.Polynomial.rankThreeDirectionDefect,
      Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_one, pow_two]
  ring

set_option maxHeartbeats 4000000 in
theorem coeff_three_rankThreeEtaNumeratorPolynomial_unit_of_homogeneous_S_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0)
    (hS : S = 0) :
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      A B C 1 Q R S).coeff 3 =
      C * Q * (Q + 1) * (A + B + C - 1) := by
  have hR : R = -(1 + Q) := by
    rw [hS] at hsum
    linear_combination hsum
  rw [hS, hR]
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
      HC4.Polynomial.rankThreeEtaNumerator,
      HC4.Polynomial.rankThreeLogProduct,
      HC4.Polynomial.rankThreeLogSum,
      Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map,
      Finset.sum_range_succ, Polynomial.coeff_X,
      Polynomial.coeff_C, Polynomial.coeff_one, pow_two]
  ring

/-- Homogeneous `R=0` next-coefficient relation. -/
theorem rankThree_terminal_homogeneous_R_zero_relation
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hsum : 1 + Q + R + S = 0)
    (hR : R = 0) :
    (B : K) * Q * (Q + 1) *
        ((A : K) + (B : K) + (C : K) - 1) *
        ((A : K) + (C : K) - (phi.natDegree : K)) = 0 := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S
  have hraw : T * Draw = Nraw := by
    simpa [T, Draw, Nraw] using
      rankThreeAutonomousPolynomial_mul_rawDenominator
        (K := K) hA hB hC (by omega) hb hden
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hT1' : T.coeff 1 = 1 := by simpa [T] using hT1
  have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop
  have hD2 : Draw.coeff 2 = 0 := by
    have h :=
      coeff_two_rankThreeEtaDenominatorPolynomial_unit_of_direction_sum_zero
        (A : K) (B : K) (C : K) Q R S hsum
    simpa [Draw, hR] using h
  have hD1 :
      Draw.coeff 1 =
        -((B : K) * Q * (Q + 1) *
          ((A : K) + (C : K)) *
          ((A : K) + (B : K) + (C : K) - 1)) := by
    simpa [Draw] using
      coeff_one_rankThreeEtaDenominatorPolynomial_unit_of_homogeneous_R_zero
        (A : K) (B : K) (C : K) Q R S hsum hR
  have hN3 :
      Nraw.coeff 3 =
        (B : K) * Q * (Q + 1) *
          ((A : K) + (B : K) + (C : K) - 1) := by
    simpa [Nraw] using
      coeff_three_rankThreeEtaNumeratorPolynomial_unit_of_homogeneous_R_zero
        (A : K) (B : K) (C : K) Q R S hsum hR
  have hshape' := hshape
  rw [hT1'] at hshape'
  have hrawShape :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw = Nraw := by
    exact (congrArg (fun U : Polynomial K => U * Draw) hshape'.symm).trans hraw
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 3) hrawShape
  change
    ((Polynomial.C 1 * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw).coeff 3 =
      Nraw.coeff 3 at hcoeff
  rw [add_mul, Polynomial.coeff_add] at hcoeff
  simp only [mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul'] at hcoeff
  norm_num at hcoeff
  rw [hD2, hD1, hN3] at hcoeff
  linear_combination
    (((A : K) + (C : K)) *
      ((B : K) * Q * (Q + 1) *
        ((A : K) + (B : K) + (C : K) - 1))) * htop' +
      (phi.natDegree : K) * hcoeff

/-- Homogeneous `S=0` next-coefficient relation. -/
theorem rankThree_terminal_homogeneous_S_zero_relation
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hsum : 1 + Q + R + S = 0)
    (hS : S = 0) :
    (C : K) * Q * (Q + 1) *
        ((A : K) + (B : K) + (C : K) - 1) *
        ((A : K) + (B : K) - (phi.natDegree : K)) = 0 := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S
  have hraw : T * Draw = Nraw := by
    simpa [T, Draw, Nraw] using
      rankThreeAutonomousPolynomial_mul_rawDenominator
        (K := K) hA hB hC (by omega) hb hden
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hT1' : T.coeff 1 = 1 := by simpa [T] using hT1
  have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop
  have hD2 : Draw.coeff 2 = 0 := by
    have h :=
      coeff_two_rankThreeEtaDenominatorPolynomial_unit_of_direction_sum_zero
        (A : K) (B : K) (C : K) Q R S hsum
    simpa [Draw, hS] using h
  have hD1 :
      Draw.coeff 1 =
        -((C : K) * Q * (Q + 1) *
          ((A : K) + (B : K)) *
          ((A : K) + (B : K) + (C : K) - 1)) := by
    simpa [Draw] using
      coeff_one_rankThreeEtaDenominatorPolynomial_unit_of_homogeneous_S_zero
        (A : K) (B : K) (C : K) Q R S hsum hS
  have hN3 :
      Nraw.coeff 3 =
        (C : K) * Q * (Q + 1) *
          ((A : K) + (B : K) + (C : K) - 1) := by
    simpa [Nraw] using
      coeff_three_rankThreeEtaNumeratorPolynomial_unit_of_homogeneous_S_zero
        (A : K) (B : K) (C : K) Q R S hsum hS
  have hshape' := hshape
  rw [hT1'] at hshape'
  have hrawShape :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw = Nraw := by
    exact (congrArg (fun U : Polynomial K => U * Draw) hshape'.symm).trans hraw
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 3) hrawShape
  change
    ((Polynomial.C 1 * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw).coeff 3 =
      Nraw.coeff 3 at hcoeff
  rw [add_mul, Polynomial.coeff_add] at hcoeff
  simp only [mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul'] at hcoeff
  norm_num at hcoeff
  rw [hD2, hD1, hN3] at hcoeff
  linear_combination
    (((A : K) + (B : K)) *
      ((C : K) * Q * (Q + 1) *
        ((A : K) + (B : K) + (C : K) - 1))) * htop' +
      (phi.natDegree : K) * hcoeff

end

end HC4.RationalRigidity
