import HC4.RationalRigidity.RankThreeQuadraticTopRelation
import HC4.Polynomial.AutonomousODERootMultiplicity
import Mathlib.Tactic

/-!
# A18.5.37: every nonzero rank-three source root has full multiplicity

A18.5.35 gives the global quadratic top relation

    A₂ * deg(phi) + 1 = 0.

A18.5.36 gives, at any nonzero root of multiplicity `M`, the local pole-order
relation

    A₂ * M + 1 = 0.

The coefficient `A₂` cannot vanish, so the two relations force
`M = deg(phi)`.  Thus the nonzero root manufactured by A18.5.28 already
accounts for the entire degree of the coefficient polynomial.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Full root-multiplicity saturation for a genuine rank-three terminal.** -/
theorem exists_rankThree_full_multiplicity_root
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    ∃ alpha : K, ∃ n : ℕ, ∃ q : Polynomial K,
      alpha ≠ 0 ∧ q.coeff 0 ≠ 0 ∧
        HC4.Polynomial.translatePolynomial alpha phi =
          Polynomial.X ^ (n + 1) * q ∧
        n + 1 = phi.natDegree := by
  rcases exists_rankThreeAutonomousPolynomial_unit_linear_top_relation
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨hPone, hphi1, b, hb, hden, hidentity, hdegT, hT0, hT1, htop⟩

  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b

  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphiDeg

  have hquad :
      HC4.Polynomial.QuadraticAutonomousLogODE
        (T.coeff 2) (T.coeff 1) phi := by
    apply quadraticAutonomousLogODE_of_degree_le_two_ratFunc_identity hphi
    · simpa [T] using hdegT
    · simpa [T] using hT0
    · simpa [T] using hidentity

  rcases HC4.Polynomial.exists_nonzero_root_multiplicity_factorisation
      (K := K) hphiDeg hphi0 with
    ⟨alpha, n, q, halpha, hq0, hfactor⟩

  have hroot :
      T.coeff 2 * (((n + 1 : ℕ) : K)) + 1 = 0 :=
    HC4.Polynomial.quadraticAutonomous_root_multiplicity_relation
      halpha hq0 hfactor hquad

  have htop' :
      T.coeff 2 * (phi.natDegree : K) + 1 = 0 := by
    simpa [T] using htop

  have hA2 : T.coeff 2 ≠ 0 := by
    intro hz
    rw [hz] at htop'
    simp at htop'

  have hmul :
      T.coeff 2 * (phi.natDegree : K) =
        T.coeff 2 * (((n + 1 : ℕ) : K)) := by
    linear_combination htop' - hroot
  have hcast :
      (phi.natDegree : K) = (((n + 1 : ℕ) : K)) :=
    mul_left_cancel₀ hA2 hmul
  have hdegree : n + 1 = phi.natDegree := by
    exact_mod_cast hcast.symm

  exact ⟨alpha, n, q, halpha, hq0, hfactor, hdegree⟩

end

end HC4.RationalRigidity
