import HC4.RationalRigidity.RankThreeQuadraticTopRelation
import Mathlib.Tactic

/-!
# A18.5.41: highest rank-three direction coefficient

After the omitted-coordinate step has become primitive, write the rank-three
direction as

    w = (1,Q,R,S)

and let `D = natDegree phi`.  The highest relevant coefficients of the raw
autonomous target are particularly simple:

    coeff_5 N_raw = -H,
    coeff_3 D_raw =  H,
    coeff_4 D_raw =  0,

where

    H = Q R S (1 + Q + R + S).

A18.5.35 gives the polynomial target

    T = X + A₂ X²,
    A₂ D + 1 = 0.

The exact identity `T * D_raw = N_raw` therefore gives
`(A₂ + 1) H = 0`.  Eliminating `A₂` division-free yields

    (D - 1) Q R S (1 + Q + R + S) = 0.

Thus a terminal of degree bigger than one either has an unchanged transverse
coordinate or its affine direction preserves ordinary degree.  This is the
finite split immediately preceding the terminal pencil cases.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 6000000

/-- Highest coefficient of the raw rank-three numerator for primitive
longitudinal direction. -/
theorem coeff_five_rankThreeEtaNumeratorPolynomial_unit
    (A B C Q R S : K) :
    (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
      A B C 1 Q R S).coeff 5 =
      -(Q * R * S * (1 + Q + R + S)) := by
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

/-- Cubic coefficient of the raw denominator. -/
theorem coeff_three_rankThreeEtaDenominatorPolynomial_unit
    (A B C Q R S : K) :
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      A B C 1 Q R S).coeff 3 =
      Q * R * S * (1 + Q + R + S) := by
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

/-- The raw denominator has no quartic coefficient. -/
theorem coeff_four_rankThreeEtaDenominatorPolynomial_unit
    (A B C Q R S : K) :
    (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
      A B C 1 Q R S).coeff 4 = 0 := by
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

/-- **Highest-direction terminal relation.** -/
theorem rankThree_terminal_highest_direction_relation
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    (((phi.natDegree : K) - 1) *
      (Q * R * S * (1 + Q + R + S))) = 0 := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, hphi1, b, hb, hden, hidentity, hdegT, hT0, hT1, htop⟩
  subst P

  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S
  let H : K := Q * R * S * (1 + Q + R + S)

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
  have htop' :
      T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop
  have hD3 : Draw.coeff 3 = H := by
    simpa [Draw, H] using
      coeff_three_rankThreeEtaDenominatorPolynomial_unit
        (A : K) (B : K) (C : K) Q R S
  have hD4 : Draw.coeff 4 = 0 := by
    simpa [Draw] using
      coeff_four_rankThreeEtaDenominatorPolynomial_unit
        (A : K) (B : K) (C : K) Q R S
  have hN5 : Nraw.coeff 5 = -H := by
    simpa [Nraw, H] using
      coeff_five_rankThreeEtaNumeratorPolynomial_unit
        (A : K) (B : K) (C : K) Q R S

  have hshape' := hshape
  rw [hT1'] at hshape'
  have hrawShape :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw = Nraw := by
    exact (congrArg (fun U : Polynomial K => U * Draw) hshape'.symm).trans hraw
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 5) hrawShape
  change
    ((Polynomial.C 1 * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw).coeff 5 =
      Nraw.coeff 5 at hcoeff
  rw [add_mul, Polynomial.coeff_add] at hcoeff
  simp only [mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, Polynomial.coeff_X_pow_mul'] at hcoeff
  norm_num at hcoeff
  rw [hD3, hD4, hN5] at hcoeff

  dsimp [H] at hcoeff ⊢
  linear_combination
    -(Q * R * S * (1 + Q + R + S)) * htop' +
      (phi.natDegree : K) * hcoeff

end

end HC4.RationalRigidity