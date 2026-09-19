import HC4.RationalRigidity.RankThreeAffineTwoFixedEqualitiesImpossible
import Mathlib.Tactic

/-!
# Cyclic affine two-fixed terminal contradictions

The existing affine RationalRigidity endgame treats the orientation
`R = S = 0`, leaving `Q` active.  The rank-three autonomous identity is cyclic
in the three transverse endpoint/direction pairs, so final assembly also needs
the two literal companion orientations.

No coordinate permutation of the Newton carrier is performed here.  These are
small scalar theorems at the already-established terminal-certificate level.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 6000000 in
/-- Coefficient three when `Q = R = 0`, leaving only `S` active. -/
theorem coeff_three_rankThree_raw_first_two_fixed
    (A B C S t : K) :
    (((Polynomial.C 1 * Polynomial.X +
          Polynomial.C t * Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          A B C 1 0 0 S -
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          A B C 1 0 0 S).coeff 3) =
      -(A * B * S * (S + 1) * (A * t + B * t - t - 1)) := by
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

set_option maxHeartbeats 6000000 in
/-- Coefficient three when `Q = S = 0`, leaving only `R` active. -/
theorem coeff_three_rankThree_raw_outer_two_fixed
    (A B C R t : K) :
    (((Polynomial.C 1 * Polynomial.X +
          Polynomial.C t * Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          A B C 1 0 R 0 -
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          A B C 1 0 R 0).coeff 3) =
      -(A * C * R * (R + 1) * (A * t + C * t - t - 1)) := by
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

/-- A terminal with `Q = R = 0` is impossible when `S` is neither zero nor
`-1`. -/
theorem rankThree_terminal_first_two_fixed_impossible
    {A B C P : ℕ} {S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) 0 0 S)
    (hS : S ≠ 0)
    (hSone : S + 1 ≠ 0) : False := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨_hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 0 S b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 0 S
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 0 S
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
  rw [coeff_three_rankThree_raw_first_two_fixed
    (A : K) (B : K) (C : K) S (T.coeff 2)] at hcoeff
  simp only [neg_eq_zero] at hcoeff
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have hpref : (A : K) * (B : K) * S * (S + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hA0 hB0) hS) hSone
  have hcoeff' :
      ((A : K) * (B : K) * S * (S + 1)) *
        ((A : K) * T.coeff 2 + (B : K) * T.coeff 2 -
          T.coeff 2 - 1) = 0 := by
    simpa [mul_assoc] using hcoeff
  have hfactor :
      (A : K) * T.coeff 2 + (B : K) * T.coeff 2 -
          T.coeff 2 - 1 = 0 :=
    (mul_eq_zero.mp hcoeff').resolve_left hpref
  have ht : T.coeff 2 ≠ 0 := by
    intro ht0
    rw [ht0] at htop'
    simp at htop'
  have hsum0 :
      T.coeff 2 *
        ((A : K) + (B : K) + (phi.natDegree : K) - 1) = 0 := by
    calc
      T.coeff 2 * ((A : K) + (B : K) + (phi.natDegree : K) - 1) =
        ((A : K) * T.coeff 2 + (B : K) * T.coeff 2 -
            T.coeff 2 - 1) +
          (T.coeff 2 * (phi.natDegree : K) + 1) := by ring
      _ = 0 := by rw [hfactor, htop']; simp
  have hsum :
      (A : K) + (B : K) + (phi.natDegree : K) = 1 := by
    have hz := (mul_eq_zero.mp hsum0).resolve_left ht
    linear_combination hz
  have hsumNat : A + B + phi.natDegree = 1 := by
    exact_mod_cast hsum
  omega

/-- A terminal with `Q = S = 0` is impossible when `R` is neither zero nor
`-1`. -/
theorem rankThree_terminal_outer_two_fixed_impossible
    {A B C P : ℕ} {R : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) 0 R 0)
    (hR : R ≠ 0)
    (hRone : R + 1 ≠ 0) : False := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨_hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  subst P
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 R 0 b
  let Draw := HC4.Polynomial.rankThreeEtaDenominatorPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 R 0
  let Nraw := HC4.Polynomial.rankThreeEtaNumeratorPolynomial
    (A : K) (B : K) (C : K) (1 : K) 0 R 0
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
  rw [coeff_three_rankThree_raw_outer_two_fixed
    (A : K) (B : K) (C : K) R (T.coeff 2)] at hcoeff
  simp only [neg_eq_zero] at hcoeff
  have hA0 : (A : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA)
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hpref : (A : K) * (C : K) * R * (R + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hA0 hC0) hR) hRone
  have hcoeff' :
      ((A : K) * (C : K) * R * (R + 1)) *
        ((A : K) * T.coeff 2 + (C : K) * T.coeff 2 -
          T.coeff 2 - 1) = 0 := by
    simpa [mul_assoc] using hcoeff
  have hfactor :
      (A : K) * T.coeff 2 + (C : K) * T.coeff 2 -
          T.coeff 2 - 1 = 0 :=
    (mul_eq_zero.mp hcoeff').resolve_left hpref
  have ht : T.coeff 2 ≠ 0 := by
    intro ht0
    rw [ht0] at htop'
    simp at htop'
  have hsum0 :
      T.coeff 2 *
        ((A : K) + (C : K) + (phi.natDegree : K) - 1) = 0 := by
    calc
      T.coeff 2 * ((A : K) + (C : K) + (phi.natDegree : K) - 1) =
        ((A : K) * T.coeff 2 + (C : K) * T.coeff 2 -
            T.coeff 2 - 1) +
          (T.coeff 2 * (phi.natDegree : K) + 1) := by ring
      _ = 0 := by rw [hfactor, htop']; simp
  have hsum :
      (A : K) + (C : K) + (phi.natDegree : K) = 1 := by
    have hz := (mul_eq_zero.mp hsum0).resolve_left ht
    linear_combination hz
  have hsumNat : A + C + phi.natDegree = 1 := by
    exact_mod_cast hsum
  omega

/-- Equality-form wrapper for `Q = R = 0`. -/
theorem rankThree_terminal_first_two_fixed_impossible_of_eq
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hQ : Q = 0) (hR : R = 0)
    (hS : S ≠ 0) (hSone : S + 1 ≠ 0) : False := by
  subst Q
  subst R
  exact rankThree_terminal_first_two_fixed_impossible
    hA hB hC hP hphiDeg hphi0 hcert hS hSone

/-- Equality-form wrapper for `Q = S = 0`. -/
theorem rankThree_terminal_outer_two_fixed_impossible_of_eq
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S)
    (hQ : Q = 0) (hS : S = 0)
    (hR : R ≠ 0) (hRone : R + 1 ≠ 0) : False := by
  subst Q
  subst S
  exact rankThree_terminal_outer_two_fixed_impossible
    hA hB hC hP hphiDeg hphi0 hcert hR hRone

end

end HC4.RationalRigidity
