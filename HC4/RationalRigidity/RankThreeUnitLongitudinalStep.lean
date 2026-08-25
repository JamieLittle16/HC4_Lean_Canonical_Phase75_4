import HC4.RationalRigidity.PolynomialAutonomousQuadraticExtraction
import HC4.Polynomial.ComplementaryEdgeRigidity
import Mathlib.Tactic

/-!
# A18.5.31: a genuine rank-three terminal has unit omitted-coordinate step

For a polynomial rank-three terminal let `P > 0` be the natural step in the
coordinate omitted by the rank-three endpoint.  A18.5.27 proves that the
linear coefficient of the polynomial autonomous target is exactly `1/P`.
A18.5.29 bounds that target by degree two, and A18.5.30 turns it into the
Phase-77 quadratic autonomous ODE.

On the source side, write the nonconstant coefficient polynomial canonically
as

    phi = C(phi(0)) + X^m q,

where `m > 0` is its least positive exponent and `q(0) != 0`.  Phase 77 says
the same linear autonomous coefficient is exactly `m`.  Therefore

    m = 1/P,

so in characteristic zero `P*m = 1`.  Since `P,m` are positive naturals,
both are one.  In particular the source edge has a nonzero linear
coefficient.
-/

namespace HC4.RationalRigidity

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Unit longitudinal-step theorem.**

Every genuine positive rank-three polynomial terminal has omitted-coordinate
step one; equivalently its source coefficient polynomial has least positive
exponent one. -/
theorem rankThree_unit_longitudinal_step_of_certificate
    {A B C P : ℕ} {Q R S : K} {phi : Polynomial K}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hP : 0 < P)
    (hphiDeg : 0 < phi.natDegree)
    (hphi0 : phi.coeff 0 ≠ 0)
    (hcert : HasRankThreePolynomialTerminalCertificate
      (phi := phi) (A : K) (B : K) (C : K) (P : K) Q R S) :
    P = 1 ∧ phi.coeff 1 ≠ 0 := by
  rcases exists_rankThreeAutonomousPolynomial_degree_le_two
      hA hB hC hP hphiDeg hphi0 hcert with
    ⟨b, hb, hden, hidentity, hdegT⟩

  let T := rankThreeAutonomousPolynomial
    (A : K) (B : K) (C : K) (P : K) Q R S b

  have hcoeff := rankThreeAutonomousPolynomial_coeff_zero_one
    (K := K) hA hB hC hP hb hden
  have hT0 : T.coeff 0 = 0 := by
    simpa [T] using hcoeff.1
  have hT1 : T.coeff 1 = (P : K)⁻¹ := by
    simpa [T] using hcoeff.2

  have hphi : phi ≠ 0 := by
    intro hz
    subst phi
    simp at hphiDeg

  have hquad :
      HC4.Polynomial.QuadraticAutonomousLogODE
        (T.coeff 2) (T.coeff 1) phi := by
    apply quadraticAutonomousLogODE_of_degree_le_two_ratFunc_identity
      hphi
    · simpa [T] using hdegT
    · exact hT0
    · simpa [T] using hidentity

  have hnonconstant : phi ≠ Polynomial.C (phi.coeff 0) := by
    intro hconst
    rw [hconst] at hphiDeg
    simp at hphiDeg

  rcases HC4.Polynomial.exists_positive_tail_factorisation
      (K := K) (phi := phi) hnonconstant with
    ⟨m, q, hm, hq0, hphiForm⟩

  have hquadLocal :
      HC4.Polynomial.QuadraticAutonomousLogODE
        (T.coeff 2) (T.coeff 1)
        (Polynomial.C (phi.coeff 0) + Polynomial.X ^ m * q) := by
    rw [← hphiForm]
    exact hquad

  have hlinear : T.coeff 1 = (m : K) :=
    HC4.Polynomial.quadraticAutonomous_linearCoefficient_eq
      (A := T.coeff 2) (B := T.coeff 1)
      (c := phi.coeff 0) (q := q) (m := m)
      hm hphi0 hq0 hquadLocal

  have hinv : (P : K)⁻¹ = (m : K) := hT1.symm.trans hlinear
  have hP0 : (P : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hP)
  have hmulK : (P : K) * (m : K) = 1 := by
    calc
      (P : K) * (m : K) = (P : K) * (P : K)⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel₀ hP0
  have hmulNat : P * m = 1 := by
    exact_mod_cast hmulK
  have hones : P = 1 ∧ m = 1 := Nat.mul_eq_one.mp hmulNat
  have hPone : P = 1 := hones.1
  have hmone : m = 1 := hones.2

  have hphi1 : phi.coeff 1 ≠ 0 := by
    rw [hphiForm, hmone]
    simp [hq0]

  exact ⟨hPone, hphi1⟩

end

end HC4.RationalRigidity
