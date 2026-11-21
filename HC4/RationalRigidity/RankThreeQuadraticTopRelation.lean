import HC4.RationalRigidity.RankThreeUnitLongitudinalStep
import Mathlib.Tactic

/-!
# A18.5.35: the rank-three quadratic target has unit linear term and exact top relation

A18.5.31 forces the omitted-coordinate edge step `P` to be one.  Therefore
A18.5.27's linear target coefficient `1/P` is literally one.  A18.5.29 and
A18.5.30 place the target in Phase 77's quadratic ODE, whose top-degree
coefficient identity is

    A * deg(phi) + B = 0.

Hence every genuine rank-three terminal carries a concrete polynomial target

    T(rho) = rho + A rho^2

with

    A * deg(phi) + 1 = 0.

This is the exact scalar form needed by the final rank-three pencil/asymptotic
case split.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Complete quadratic scalar package extracted from a genuine rank-three
polynomial terminal certificate. -/
theorem exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    P = 1 ∧ phi.coeff 1 ≠ 0 ∧
      ∃ b : K, b ≠ 0 ∧
        rankThreeTargetDenominator
            (A : K) (B : K) (C : K) (P : K) Q R S = Polynomial.C b ∧
        let T := rankThreeAutonomousPolynomial
          (A : K) (B : K) (C : K) (P : K) Q R S b
        Polynomial.aeval (logarithmicSourceRatFunc phi) T =
            logarithmicSourceEtaRatFunc phi ∧
          T.natDegree ≤ 2 ∧
          T.coeff 0 = 0 ∧
          T.coeff 1 = 1 ∧
          T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
  have hunit := rankThree_unit_longitudinal_step_of_certificate
    hA hB hC hP hphiDeg hphi0 hcert
  rcases hunit with ⟨hPone, hphi1⟩
  rcases exists_rankThreeAutonomousPolynomial_degree_le_two
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨b, hb, hden, hidentity, hdegT⟩
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b
  have hcoeff := rankThreeAutonomousPolynomial_coeff_zero_one
    (K := K) hA hB hC hP hb hden
  have hT0 : T.coeff 0 = 0 := by simpa [T] using hcoeff.1
  have hT1raw : T.coeff 1 = (P : K)⁻¹ := by simpa [T] using hcoeff.2
  have hT1 : T.coeff 1 = 1 := by
    rw [hT1raw, hPone]
    simp
  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphiDeg
  have hquad :
      HC4.Polynomial.QuadraticAutonomousLogODE
        (T.coeff 2) (T.coeff 1) phi := by
    apply quadraticAutonomousLogODE_of_degree_le_two_ratFunc_identity hphi
    · simpa [T] using hdegT
    · exact hT0
    · simpa [T] using hidentity
  have htop := HC4.Polynomial.quadraticAutonomous_top_relation
    (A := T.coeff 2) (B := T.coeff 1) hphiDeg hquad
  rw [hT1] at htop
  refine ⟨hPone, hphi1, b, hb, hden, ?_⟩
  dsimp only
  exact ⟨hidentity, hdegT, hT0, hT1, htop⟩

end

end HC4.RationalRigidity
