import HC4.RationalRigidity.PolynomialAutonomousQuadraticExtraction
import HC4.Polynomial.ComplementaryEdgeRigidity
import Mathlib.Tactic

/-!
# A18.5.31: the first rank-three edge step is primitive

For the polynomial autonomous target produced by a rank-three edge,
A18.5.27 computes the linear coefficient geometrically as `1/P`, where `P>0`
is the increase of the omitted coordinate along one coefficient step.

After A18.5.29--30 the same target is in the exact Phase-77 quadratic ODE
interface.  Factoring the nonconstant source polynomial at its least positive
term,

    phi = C(phi(0)) + X^m q,   m>0, q(0)!=0,

Phase 77 proves that the linear autonomous coefficient is `m`.
Consequently `m = 1/P`.  Characteristic zero and positivity force

    P = 1,  m = 1.

This is the primitive longitudinal step needed by the terminal rank-three
pencil calculation.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Primitive omitted-coordinate step and primitive first source layer.** -/
theorem rankThreeTerminal_primitive_step
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    P = 1 ∧
      ∃ q : Polynomial K,
        q.coeff 0 ≠ 0 ∧
        phi = Polynomial.C (phi.coeff 0) + Polynomial.X * q := by
  have hnonconstant : phi ≠ Polynomial.C (phi.coeff 0) := by
    intro hconst
    rw [hconst] at hphiDeg
    simp at hphiDeg
  rcases HC4.Polynomial.exists_positive_tail_factorisation
      (K := K) hnonconstant with
    ⟨m, q, hm, hq0, hphi⟩

  rcases exists_rankThreeAutonomousPolynomial_degree_le_two
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨b, hb, hden, hidentity, hTdeg⟩
  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b

  have hcoeff := rankThreeAutonomousPolynomial_coeff_zero_one
    (K := K) hA hB hC hP hb hden
  have hT0 : T.coeff 0 = 0 := by simpa [T] using hcoeff.1
  have hT1 : T.coeff 1 = (P : K)⁻¹ := by simpa [T] using hcoeff.2
  have hdeg : T.natDegree ≤ 2 := by simpa [T] using hTdeg
  have hquad := quadraticAutonomousLogODE_of_degree_le_two_ratFunc_identity
    (K := K)
    (T := T) (phi := phi)
    (by
      intro hz
      subst phi
      simp at hphiDeg)
    hdeg hT0 (by simpa [T] using hidentity)

  have hquadLocal :
      HC4.Polynomial.QuadraticAutonomousLogODE
        (T.coeff 2) (T.coeff 1)
        (Polynomial.C (phi.coeff 0) + Polynomial.X ^ m * q) := by
    rw [← hphi]
    exact hquad
  have hBsource :=
    HC4.Polynomial.quadraticAutonomous_linearCoefficient_eq
      (A := T.coeff 2) (B := T.coeff 1)
      (c := phi.coeff 0) (q := q) (m := m)
      hm hphi0 hq0 hquadLocal
  have hInv : (P : K)⁻¹ = (m : K) := by
    rw [← hT1]
    exact hBsource
  have hP0 : (P : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hProdK : (P : K) * (m : K) = 1 := by
    calc
      (P : K) * (m : K) = (P : K) * (P : K)⁻¹ := by rw [hInv]
      _ = 1 := mul_inv_cancel₀ hP0
  have hProdNat : P * m = 1 := by exact_mod_cast hProdK
  have hPone : P = 1 := by omega
  have hmone : m = 1 := by omega
  refine ⟨hPone, q, hq0, ?_⟩
  rw [hphi, hmone]
  simp

end

end HC4.RationalRigidity
