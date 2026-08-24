import HC4.RationalRigidity.RankThreeTargetDegreeBound
import HC4.Polynomial.AutonomousODEQuadraticRigidity
import Mathlib.Tactic

/-!
# A18.5.30: degree-two polynomial autonomous targets enter Phase 77

A polynomial autonomous target of degree at most two and zero constant term is
literally

    B X + A X^2.

The RatFunc identity `R(E(phi)/phi)=eta` can then be cleared uniformly at
homogenising degree `2`, even if `A=0`.  The generic cleared-substitution
theorem from Phase 88 gives exactly

    logarithmicEtaNumerator phi
      = C A * E(phi)^2 + C B * (phi * E(phi)),

which is `QuadraticAutonomousLogODE A B phi` from Phase 77.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Every polynomial of degree at most two is determined by coefficients
`0,1,2`; with zero constant term it has the displayed linear/quadratic form. -/
theorem eq_linear_add_quadratic_of_natDegree_le_two
    {T : Polynomial K}
    (hdeg : T.natDegree ≤ 2)
    (hzero : T.coeff 0 = 0) :
    T = Polynomial.C (T.coeff 1) * Polynomial.X +
      Polynomial.C (T.coeff 2) * Polynomial.X ^ 2 := by
  apply Polynomial.ext
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp [hzero]
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases hn2 : n = 2
  · subst n
    simp
  have hn : 2 < n := by omega
  have hcoeff : T.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hn)
  simp [hcoeff, hn0, hn1, hn2]

/-- Degree-two cleared substitution of a zero-constant polynomial is the
ordinary homogenised quadratic expression. -/
theorem clearedPolynomialSubstitution_two_of_coeff_zero
    {T N D : Polynomial K}
    (hdeg : T.natDegree ≤ 2)
    (hzero : T.coeff 0 = 0) :
    clearedPolynomialSubstitution 2 T N D =
      Polynomial.C (T.coeff 1) * N * D +
        Polynomial.C (T.coeff 2) * N ^ 2 := by
  have hshape := eq_linear_add_quadratic_of_natDegree_le_two hdeg hzero
  rw [hshape]
  classical
  unfold clearedPolynomialSubstitution
  simp [Polynomial.sum_def]
  ring

/-- **RatFunc polynomial identity -> Phase-77 quadratic ODE**, uniformly for
linear or quadratic targets. -/
theorem quadraticAutonomousLogODE_of_degree_le_two_ratFunc_identity
    {T phi : Polynomial K}
    (hphi : phi ≠ 0)
    (hdeg : T.natDegree ≤ 2)
    (hzero : T.coeff 0 = 0)
    (hidentity :
      Polynomial.aeval (logarithmicSourceRatFunc phi) T =
        logarithmicSourceEtaRatFunc phi) :
    HC4.Polynomial.QuadraticAutonomousLogODE
      (T.coeff 2) (T.coeff 1) phi := by
  let E := HC4.Polynomial.eulerDerivative phi
  let H := HC4.Polynomial.logarithmicEtaNumerator phi
  have hRho :
      logarithmicSourceRatFunc phi =
        algebraMap (Polynomial K) (RatFunc K) E /
          algebraMap (Polynomial K) (RatFunc K) phi := by
    rfl
  have hEta :
      logarithmicSourceEtaRatFunc phi =
        algebraMap (Polynomial K) (RatFunc K) H /
          (algebraMap (Polynomial K) (RatFunc K) phi) ^ 2 := by
    have hraw := logarithmicSourceEtaRatFunc_eq_raw phi hphi
    simpa [polynomialPairRatFunc, H] using hraw
  have hcross :
      Polynomial.aeval (logarithmicSourceRatFunc phi) T =
        logarithmicSourceEtaRatFunc phi *
          Polynomial.aeval (logarithmicSourceRatFunc phi) (1 : Polynomial K) := by
    simpa using hidentity
  have hcleared :=
    clearedPolynomialSubstitution_identity_of_ratFunc
      (K := K)
      (rho := logarithmicSourceRatFunc phi)
      (eta := logarithmicSourceEtaRatFunc phi)
      (A := T) (B := (1 : Polynomial K))
      (N := E) (D := phi) (H := H) (m := 2)
      hphi hRho hEta hdeg (by simp) hcross
  rw [clearedPolynomialSubstitution_one] at hcleared
  have hphi2 : phi ^ 2 ≠ 0 := pow_ne_zero 2 hphi
  have hcancel : clearedPolynomialSubstitution 2 T E phi = H := by
    apply mul_right_cancel₀ hphi2
    calc
      clearedPolynomialSubstitution 2 T E phi * phi ^ 2 =
          H * phi ^ 2 := by simpa using hcleared
      _ = H * phi ^ 2 := rfl
  rw [clearedPolynomialSubstitution_two_of_coeff_zero hdeg hzero] at hcancel
  unfold HC4.Polynomial.QuadraticAutonomousLogODE
  dsimp [E, H] at hcancel ⊢
  calc
    HC4.Polynomial.logarithmicEtaNumerator phi =
        Polynomial.C (T.coeff 1) * HC4.Polynomial.eulerDerivative phi * phi +
          Polynomial.C (T.coeff 2) *
            (HC4.Polynomial.eulerDerivative phi) ^ 2 := hcancel.symm
    _ = Polynomial.C (T.coeff 2) *
          (HC4.Polynomial.eulerDerivative phi) ^ 2 +
        Polynomial.C (T.coeff 1) *
          HC4.Polynomial.logarithmicEtaOverRhoDenominator phi := by
      unfold HC4.Polynomial.logarithmicEtaOverRhoDenominator
      ring

end

end HC4.RationalRigidity
