import HC4.RationalRigidity.RankThreeHomogeneousDirectionFixed
import Mathlib.Tactic

/-!
# A18.5.60: the next homogeneous relation when `Q = 0`

A18.5.59 proves that at least one transverse direction coefficient vanishes.
This file opens the `Q = 0` branch one coefficient further.  Under

    1 + Q + R + S = 0,

we have `S = -(1+R)`.  The raw target coefficients simplify to

    coeff_2 D_raw = 0,
    coeff_1 D_raw = -A R(R+1)(B+C)(A+B+C-1),
    coeff_3 N_raw =  A R(R+1)(A+B+C-1).

Coefficient three of `T * D_raw = N_raw`, together with
`t2 * deg(phi) + 1 = 0`, therefore gives

    A R(R+1)(A+B+C-1)(B+C-deg(phi)) = 0.

For the supported terminal all scalar factors surrounding `R(R+1)` are
strictly nonzero.  This is the relation that forces the unit starting
coordinate in the `sp`/`rq` endpoint cases.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/- Linear denominator coefficient in the homogeneous `Q=0` branch. -/
set_option maxHeartbeats 6000000 in
theorem coeff_one_rankThreeEtaDenominatorPolynomial_unit_of_homogeneous_Q_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0)
    (hQ : Q = 0) :
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      A B C 1 Q R S).coeff 1 =
      -(A * R * (R + 1) * (B + C) * (A + B + C - 1)) := by
  have hS : S = -(1 + R) := by
    rw [hQ] at hsum
    linear_combination hsum
  rw [hQ, hS]
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

/- Cubic numerator coefficient in the homogeneous `Q=0` branch. -/
set_option maxHeartbeats 4000000 in
theorem coeff_three_rankThreeEtaNumeratorPolynomial_unit_of_homogeneous_Q_zero
    (A B C Q R S : K)
    (hsum : 1 + Q + R + S = 0)
    (hQ : Q = 0) :
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      A B C 1 Q R S).coeff 3 =
      A * R * (R + 1) * (A + B + C - 1) := by
  have hS : S = -(1 + R) := by
    rw [hQ] at hsum
    linear_combination hsum
  rw [hQ, hS]
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

/-- **Homogeneous `Q=0` next-coefficient relation.** -/
theorem rankThree_terminal_homogeneous_Q_zero_relation
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hsum : 1 + Q + R + S = 0)
    (hQ : Q = 0) :
    (A : K) * R * (R + 1) *
        ((A : K) + (B : K) + (C : K) - 1) *
        ((B : K) + (C : K) - (phi.natDegree : K)) = 0 := by
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
    simpa [Draw, hQ] using h
  have hD1 :
      Draw.coeff 1 =
        -((A : K) * R * (R + 1) *
          ((B : K) + (C : K)) *
          ((A : K) + (B : K) + (C : K) - 1)) := by
    simpa [Draw] using
      coeff_one_rankThreeEtaDenominatorPolynomial_unit_of_homogeneous_Q_zero
        (A : K) (B : K) (C : K) Q R S hsum hQ
  have hN3 :
      Nraw.coeff 3 =
        (A : K) * R * (R + 1) *
          ((A : K) + (B : K) + (C : K) - 1) := by
    simpa [Nraw] using
      coeff_three_rankThreeEtaNumeratorPolynomial_unit_of_homogeneous_Q_zero
        (A : K) (B : K) (C : K) Q R S hsum hQ

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
    (((B : K) + (C : K)) *
      ((A : K) * R * (R + 1) *
        ((A : K) + (B : K) + (C : K) - 1))) * htop' +
      (phi.natDegree : K) * hcoeff

end

end HC4.RationalRigidity
