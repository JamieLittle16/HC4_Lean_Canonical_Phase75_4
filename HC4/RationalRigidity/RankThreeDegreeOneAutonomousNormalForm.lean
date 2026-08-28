import HC4.RationalRigidity.RankThreeQuadraticTopRelation
import Mathlib.Tactic

/-!
# A19.90: exact autonomous target in the degree-one rank-three terminal

The Phase-88 rank-three terminal machinery already removes every finite and
infinite denominator and produces a polynomial autonomous target.  The mature
quadratic rigidity stack then proves that a genuine terminal has primitive
omitted-coordinate step `P = 1`, zero constant target coefficient, unit linear
coefficient, target degree at most two, and

    T.coeff 2 * natDegree(phi) + 1 = 0.

When the actual coefficient polynomial has degree exactly one, as in the
surviving A19.75 lower `qs` ray, the last relation forces `T.coeff 2 = -1`.
Thus the autonomous target is not merely quadratic: it is literally

    T = X - X^2.

Substitution back into the raw target cross identity gives an exact polynomial
identity between the rank-three numerator and denominator.  This is the
coefficient-facing interface for the final balance-free endpoint arithmetic.
-/

namespace HC4.RationalRigidity

noncomputable section

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Exact degree-one autonomous normal form.**  A genuine rank-three
polynomial terminal whose source coefficient polynomial has natural degree one
has primitive longitudinal step and autonomous target exactly `X - X^2`. -/
theorem exists_rankThreeAutonomousPolynomial_eq_X_sub_X_sq_of_source_degree_one
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : phi.natDegree = 1)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    P = 1 ∧ phi.coeff 1 ≠ 0 ∧
      ∃ b : K, b ≠ 0 ∧
        rankThreeTargetDenominator
            (A : K) (B : K) (C : K) (P : K) Q R S = Polynomial.C b ∧
        Polynomial.aeval (logarithmicSourceRatFunc phi)
            (rankThreeAutonomousPolynomial
              (A : K) (B : K) (C : K) (P : K) Q R S b) =
          logarithmicSourceEtaRatFunc phi ∧
        rankThreeAutonomousPolynomial
            (A : K) (B : K) (C : K) (P : K) Q R S b =
          Polynomial.X - Polynomial.X ^ 2 := by
  have hphiPos : 0 < phi.natDegree := by omega
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiPos hphi0 hcert with
    ⟨hPone, hphi1, b, hb, hden, hidentity, hdegT, hT0, hT1, htop⟩
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b
  have hT2 : T.coeff 2 = (-1 : K) := by
    have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
      simpa [T] using htop
    rw [hphiDeg] at htop'
    norm_num at htop' ⊢
    exact eq_neg_of_add_eq_zero_left htop'
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hTexact : T = Polynomial.X - Polynomial.X ^ 2 := by
    rw [show T.coeff 1 = (1 : K) by simpa [T] using hT1, hT2] at hshape
    simpa [sub_eq_add_neg] using hshape
  refine ⟨hPone, hphi1, b, hb, hden, hidentity, ?_⟩
  simpa [T] using hTexact

/-- The exact normal form can be pushed back through the raw reduced-target
cross identity.  This exposes a literal polynomial identity for coefficient
comparison, with no RatFunc denominator left. -/
theorem exists_rankThree_raw_target_X_sub_X_sq_identity_of_source_degree_one
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : phi.natDegree = 1)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    P = 1 ∧ phi.coeff 1 ≠ 0 ∧
      (Polynomial.X - Polynomial.X ^ 2) *
          HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (A : K) (B : K) (C : K) (P : K) Q R S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (P : K) Q R S := by
  rcases exists_rankThreeAutonomousPolynomial_eq_X_sub_X_sq_of_source_degree_one
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, hphi1, b, hb, hden, _hidentity, hTexact⟩
  have hraw := rankThreeAutonomousPolynomial_mul_rawDenominator
    (K := K) hA hB hC hP hb hden
  rw [hTexact] at hraw
  exact ⟨hPone, hphi1, hraw⟩

set_option maxHeartbeats 1000000 in
/-- **Unit-step degree-one raw identity.**  This is the direct interface for
callers that already know the longitudinal step is one.  Unlike the generic
A19.90 theorem above, it never introduces an arbitrary `P`, never asks the
elaborator to recover `P` through a terminal certificate, and never builds the
`P = 1 ∧ ...` result package. -/
theorem rankThree_raw_target_X_sub_X_sq_identity_of_source_degree_one_unit_step
    {A B C : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hphiDeg : phi.natDegree = 1)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S) :
    (Polynomial.X - Polynomial.X ^ 2) *
        HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S =
      HC4.Polynomial.rankThreeEtaNumeratorPolynomial
        (A : K) (B : K) (C : K) (1 : K) Q R S := by
  have hphiPos : 0 < phi.natDegree := by omega
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      (K := K) (A := A) (B := B) (C := C) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      hA hB hC (by norm_num) hphiPos hphi0 hcert with
    ⟨_hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S b
  have hT2 : T.coeff 2 = (-1 : K) := by
    have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
      simpa [T] using htop
    rw [hphiDeg] at htop'
    norm_num at htop' ⊢
    exact eq_neg_of_add_eq_zero_left htop'
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hTexact : T = Polynomial.X - Polynomial.X ^ 2 := by
    rw [show T.coeff 1 = (1 : K) by simpa [T] using hT1, hT2] at hshape
    simpa [sub_eq_add_neg] using hshape
  have hraw := rankThreeAutonomousPolynomial_mul_rawDenominator
    (K := K) hA hB hC (by norm_num) hb hden
  rw [show rankThreeAutonomousPolynomial
      (A : K) (B : K) (C : K) (1 : K) Q R S b =
        Polynomial.X - Polynomial.X ^ 2 by simpa [T] using hTexact] at hraw
  exact hraw

set_option maxHeartbeats 1000000 in
/-- **Unit-step degree-one raw relation at `rho = 2`.**  Final endpoint
arithmetic only ever evaluates the raw target identity at `2`, so this smaller
interface avoids materialising a polynomial equality in downstream theorem
types. -/
theorem rankThree_raw_target_eval_two_of_source_degree_one_unit_step
    {A B C : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hphiDeg : phi.natDegree = 1)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (1 : K) Q R S) :
    (-2 : K) *
        Polynomial.eval (2 : K)
          (HC4.Polynomial.rankThreeEtaDenominatorPolynomial
            (A : K) (B : K) (C : K) (1 : K) Q R S) =
      Polynomial.eval (2 : K)
        (HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S) := by
  have hphiPos : 0 < phi.natDegree := by omega
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      (K := K) (A := A) (B := B) (C := C) (P := 1)
      (Q := Q) (R := R) (S := S) (phi := phi)
      hA hB hC (by norm_num) hphiPos hphi0 hcert with
    ⟨_hPone, _hphi1, b, hb, hden, _hidentity, hdegT, hT0, hT1, htop⟩
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (1 : K) Q R S b
  have hT1' : T.coeff 1 = (1 : K) := by simpa [T] using hT1
  have hT2 : T.coeff 2 = (-1 : K) := by
    have htop' : T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
      simpa [T] using htop
    rw [hphiDeg] at htop'
    norm_num at htop' ⊢
    exact eq_neg_of_add_eq_zero_left htop'
  have hshape :
      T = Polynomial.C (T.coeff 1) * Polynomial.X +
        Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 :=
    eq_linear_add_quadratic_of_natDegree_le_two
      (by simpa [T] using hdegT) (by simpa [T] using hT0)
  have hTeval : Polynomial.eval (2 : K) T = (-2 : K) := by
    rw [hshape, hT1', hT2]
    norm_num
  have hraw := rankThreeAutonomousPolynomial_mul_rawDenominator
    (K := K) hA hB hC (by norm_num) hb hden
  have hrawT :
      T * HC4.Polynomial.rankThreeEtaDenominatorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S =
        HC4.Polynomial.rankThreeEtaNumeratorPolynomial
          (A : K) (B : K) (C : K) (1 : K) Q R S := by
    simpa [T] using hraw
  have h2 := congrArg (Polynomial.eval (2 : K)) hrawT
  simp only [Polynomial.eval_mul] at h2
  rw [hTeval] at h2
  exact h2

end

end HC4.RationalRigidity
