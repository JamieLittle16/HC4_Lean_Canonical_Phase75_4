import HC4.RationalRigidity.RankThreeRootMultiplicity
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic

/-!
# A18.5.38: a rank-three terminal source is a translated pure power

A18.5.37 shows that the nonzero root furnished by algebraic closure has
multiplicity equal to the whole degree `D = natDegree phi`.  The A18.5.28
factorisation therefore reads

    translate alpha phi = X^D q.

Translation by a scalar preserves degree.  Since `q(0) != 0`, the quotient is
nonzero, and degree comparison forces `natDegree q = 0`.  Hence `q` is a
nonzero constant and the translated source is literally a scalar multiple of
`X^D`.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Translation by a scalar preserves natural degree over a field. -/
theorem natDegree_translatePolynomial
    (alpha : K) (p : Polynomial K) :
    (HC4.Polynomial.translatePolynomial alpha p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · subst p
    simp [HC4.Polynomial.translatePolynomial]
  · have hlead : p.leadingCoeff ≠ 0 :=
      (Polynomial.leadingCoeff_ne_zero).2 hp
    have hmul :
        p.leadingCoeff *
            (Polynomial.X + Polynomial.C alpha).leadingCoeff ^ p.natDegree ≠ 0 := by
      simpa using hlead
    have hcomp := Polynomial.natDegree_comp_eq_of_mul_ne_zero
      (p := p) (q := Polynomial.X + Polynomial.C alpha) hmul
    simpa [HC4.Polynomial.translatePolynomial] using hcomp

/-- **Translated pure-power reconstruction.**
Every genuine rank-three polynomial terminal has a nonzero root `alpha` such
that translation to that root is a nonzero scalar multiple of `X^D`, where
`D` is the full source degree. -/
theorem exists_rankThree_translated_pure_power
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    ∃ alpha c : K,
      alpha ≠ 0 ∧ c ≠ 0 ∧
        HC4.Polynomial.translatePolynomial alpha phi =
          Polynomial.C c * Polynomial.X ^ phi.natDegree := by
  rcases exists_rankThree_full_multiplicity_root
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨alpha, n, q, halpha, hq0, hfactor, hdegree⟩

  have hq : q ≠ 0 := by
    intro hz
    subst q
    simp at hq0

  have htransDeg :
      (HC4.Polynomial.translatePolynomial alpha phi).natDegree =
        phi.natDegree :=
    natDegree_translatePolynomial alpha phi

  have hfactorD :
      HC4.Polynomial.translatePolynomial alpha phi =
        Polynomial.X ^ phi.natDegree * q := by
    simpa [hdegree] using hfactor

  have hdegq : q.natDegree = 0 := by
    have hdeg := htransDeg
    rw [hfactorD, Polynomial.natDegree_X_pow_mul phi.natDegree hq] at hdeg
    omega

  have hqC : q = Polynomial.C (q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdegq

  refine ⟨alpha, q.coeff 0, halpha, hq0, ?_⟩
  rw [hfactorD, hqC]
  ring

end

end HC4.RationalRigidity
