import HC4.RationalRigidity.PolynomialAutonomousClearing
import HC4.Polynomial.AutonomousODERootFactorisation
import HC4.RationalRigidity.RankThreeTargetInitialSlope
import Mathlib.Tactic

/-!
# A18.5.29: the polynomial rank-three autonomous target has degree at most two

The Phase-79 pole-order theorem was already complete once a polynomial
autonomous equation and a translated nonzero-root multiplicity factorisation
were supplied.  A18.5.16 supplies the first datum from the rank-three terminal
identity; A18.5.28 supplies the second automatically from nonconstancy and a
nonzero constant coefficient of `phi`.

Thus every rank-three polynomial terminal certificate arising from a genuine
edge has target degree at most two.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Rank-three polynomial target degree bound.** -/
theorem rankThreeAutonomousPolynomial_natDegree_le_two_of_certificate
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    ∀ b : K,
      b ≠ 0 →
      rankThreeTargetDenominator
          (A : K) (B : K) (C : K) (P : K) Q R S = Polynomial.C b →
      Polynomial.aeval (logarithmicSourceRatFunc phi)
          (rankThreeAutonomousPolynomial
            (A : K) (B : K) (C : K) (P : K) Q R S b) =
        logarithmicSourceEtaRatFunc phi →
      (rankThreeAutonomousPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S b).natDegree ≤ 2 := by
  intro b hb hden hidentity
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b
  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphiDeg
  by_cases hlarge : 2 ≤ T.natDegree
  · have hode : HC4.Polynomial.ShiftedPolynomialAutonomousLogODE 0 T phi :=
      shiftedPolynomialAutonomousLogODE_zero_of_ratFunc_identity
        hphi hlarge (by simpa [T] using hidentity)
    rcases HC4.Polynomial.exists_nonzero_root_multiplicity_factorisation
        (K := K) hphiDeg hphi0 with
      ⟨alpha, n, q, halpha, hq0, hfactor⟩
    have hle :=
      HC4.Polynomial.natDegree_le_two_of_polynomialAutonomousLogODE_after_translation
        (K := K) (alpha := alpha) (R := T) (p := phi)
        (q := q) (n := n)
        halpha hq0 hfactor hode
    simpa [T] using hle
  · have hlt : T.natDegree < 2 := Nat.lt_of_not_ge hlarge
    have hle : T.natDegree ≤ 2 := by omega
    simpa [T] using hle

/-- Existential-facing form: every terminal certificate contains a concrete
constant denominator whose associated autonomous polynomial has degree at
most two. -/
theorem exists_rankThreeAutonomousPolynomial_degree_le_two
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    ∃ b : K, b ≠ 0 ∧
      rankThreeTargetDenominator
          (A : K) (B : K) (C : K) (P : K) Q R S = Polynomial.C b ∧
      Polynomial.aeval (logarithmicSourceRatFunc phi)
          (rankThreeAutonomousPolynomial
            (A : K) (B : K) (C : K) (P : K) Q R S b) =
        logarithmicSourceEtaRatFunc phi ∧
      (rankThreeAutonomousPolynomial
        (A : K) (B : K) (C : K) (P : K) Q R S b).natDegree ≤ 2 := by
  rcases hcert with ⟨b, hb, hden, hidentity⟩
  refine ⟨b, hb, hden, hidentity, ?_⟩
  exact rankThreeAutonomousPolynomial_natDegree_le_two_of_certificate
    hA hB hC hP hphiDeg hphi0
    ⟨b, hb, hden, hidentity⟩ b hb hden hidentity

end

end HC4.RationalRigidity
