import HC4.RationalRigidity.RankThreeQuadraticTopRelation
import Mathlib.Tactic

/-!
# A18.5.73a: two fixed affine directions are impossible

The genuine first-contact affine model deliberately allows nonintegral
transverse slopes, so the final contradiction must not pass through the older
integral finite-segment interface.

If two transverse affine slopes vanish, say `R = S = 0`, the cleared
rank-three identity is already decisive.  Writing the autonomous target as

    T(rho) = rho + t₂ rho²,

the coefficient-three equation is

    B C Q (Q+1) (t₂(B+C-1) - 1) = 0.

For a genuine nontrivial, non-homogeneous remaining slope (`Q != 0` and
`Q+1 != 0`) this gives `t₂(B+C-1)=1`.  The terminal top relation gives
`t₂ D = -1`, where `D = natDegree phi > 0`.  Hence

    B + C + D = 1,

contradicting positivity of `B`, `C`, and `D`.

This is the affine replacement for the old integral-line two-fixed
contradiction and introduces no divisibility hypothesis.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 6000000 in
/-- Coefficient three of the raw autonomous identity when the last two
affine-direction coordinates are fixed. -/
theorem coeff_three_rankThree_raw_two_fixed
    (A B C Q t : K) :
    (((Polynomial.C 1 * Polynomial.X +
          Polynomial.C t * Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          A B C 1 Q 0 0 -
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          A B C 1 Q 0 0).coeff 3) =
      -(B * C * Q * (Q + 1) * (B * t + C * t - t - 1)) := by
  simp (config := { maxSteps := 1000000 })
    [HC4.Polynomial.rankThreeEtaNumeratorPolynomial,
      HC4.Polynomial.rankThreeEtaDenominatorPolynomial,
      HC4.Polynomial.rankThreeEtaNumerator,
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

/-- **Affine two-fixed terminal impossibility.**

A genuine rank-three polynomial terminal cannot have two fixed transverse
directions while the remaining transverse slope is neither zero nor `-1`.
This statement is entirely at the affine/certificate level and therefore does
not assume an integral reparameterisation of the exponent line. -/
theorem rankThree_terminal_two_fixed_impossible
    {A B C P : ℕ} {Q : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q 0 0)
    (hQ : Q ≠ 0)
    (hQone : Q + 1 ≠ 0) :
    False := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨_hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P

  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q 0 0 b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q 0 0
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q 0 0

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
  have hshape' := hshape
  rw [hT1'] at hshape'
  have hrawShape :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw = Nraw :=
    (congrArg (fun U : Polynomial K => U * Draw) hshape'.symm).trans hraw
  have hzero :
      (Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw = 0 :=
    sub_eq_zero.mpr hrawShape
  have hcoeff :
      ((Polynomial.C 1 * Polynomial.X +
          Polynomial.C (T.coeff 2) * Polynomial.X ^ 2) * Draw - Nraw).coeff 3 = 0 := by
    rw [hzero]
    simp
  dsimp [Draw, Nraw] at hcoeff
  have hformula := coeff_three_rankThree_raw_two_fixed
    (A : K) (B : K) (C : K) Q (T.coeff 2)
  rw [hformula] at hcoeff
  simp only [neg_eq_zero] at hcoeff

  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hpref : (B : K) * (C : K) * Q * (Q + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hB0 hC0) hQ) hQone
  have hcoeff' :
      ((B : K) * (C : K) * Q * (Q + 1)) *
        ((B : K) * T.coeff 2 + (C : K) * T.coeff 2 -
          T.coeff 2 - 1) = 0 := by
    simpa [mul_assoc] using hcoeff
  have hfactor :
      (B : K) * T.coeff 2 + (C : K) * T.coeff 2 -
          T.coeff 2 - 1 = 0 :=
    (mul_eq_zero.mp hcoeff').resolve_left hpref

  have ht : T.coeff 2 ≠ 0 := by
    intro ht0
    rw [ht0] at htop'
    simp at htop'

  have hsum0 :
      T.coeff 2 *
        ((B : K) + (C : K) + (phi.natDegree : K) - 1) = 0 := by
    linear_combination hfactor + htop'
  have hsum :
      (B : K) + (C : K) + (phi.natDegree : K) - 1 = 0 :=
    (mul_eq_zero.mp hsum0).resolve_left ht
  have hsumK :
      (B : K) + (C : K) + (phi.natDegree : K) = 1 := by
    linear_combination hsum
  have hsumNat : B + C + phi.natDegree = 1 := by
    exact_mod_cast hsumK
  omega

end

end HC4.RationalRigidity
