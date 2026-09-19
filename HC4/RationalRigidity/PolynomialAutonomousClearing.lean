import HC4.RationalRigidity.ClearedInfinityEvaluation
import HC4.RationalRigidity.LogarithmicSourceRatFunc
import HC4.Polynomial.AutonomousODETranslation
import Mathlib.Tactic

/-!
# A18.5.16: clear a polynomial autonomous RatFunc identity

Phase 88 ends with an honest polynomial `R` satisfying

    R(E(phi)/phi) = eta,

as an equality in `RatFunc K`, where

    E(phi) = X phi',
    eta = logarithmicEtaNumerator(phi) / phi^2.

Phase 79 consumes instead the denominator-cleared polynomial equation
`ShiftedPolynomialAutonomousLogODE 0 R phi`.

The general clearing theorem already proved for the infinity chart does all
of the hard work.  We instantiate it with

    A = R,  B = 1,
    N = E(phi), D = phi,
    H = logarithmicEtaNumerator(phi),
    m = natDegree R.

It gives

    cleared(R) * phi^2 = H * phi^m.

For `m >= 2`, cancel the nonzero factor `phi^2` and identify the remaining
homogeneous substitution with Phase 79's `shiftedAutonomousClearedRHS`.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- At zero shift, Phase 79's homogenised autonomous RHS is exactly the
generic cleared polynomial substitution at `E(phi)/phi`. -/
theorem shiftedAutonomousClearedRHS_zero_eq_clearedPolynomialSubstitution
    (R phi : Polynomial K) :
    HC4.Polynomial.shiftedAutonomousClearedRHS 0 R phi =
      clearedPolynomialSubstitution R.natDegree R
        (HC4.Polynomial.eulerDerivative phi) phi := by
  classical
  unfold HC4.Polynomial.shiftedAutonomousClearedRHS
  unfold clearedPolynomialSubstitution
  dsimp only
  rw [HC4.Polynomial.shiftedEuler_zero]

/-- Clearing the constant polynomial `1` contributes only the full denominator
power. -/
theorem clearedPolynomialSubstitution_one
    (m : ℕ) (N D : Polynomial K) :
    clearedPolynomialSubstitution m (1 : Polynomial K) N D = D ^ m := by
  classical
  unfold clearedPolynomialSubstitution
  rw [show (1 : Polynomial K) = Polynomial.C 1 by simp]
  have hf :
      Polynomial.C (0 : K) * N ^ 0 * D ^ (m - 0) = 0 := by
    simp
  rw [Polynomial.sum_C_index hf]
  simp

/-- **RatFunc polynomial autonomous identity -> Phase-79 cleared ODE.**

No reduced source presentation is needed here: we deliberately return to the
raw chart `E(phi)/phi`, whose denominator is the actual polynomial `phi`.
-/
theorem shiftedPolynomialAutonomousLogODE_zero_of_ratFunc_identity
    {R phi : Polynomial K}
    (hphi : phi ≠ 0)
    (hdeg : 2 ≤ R.natDegree)
    (hidentity :
      Polynomial.aeval (logarithmicSourceRatFunc phi) R =
        logarithmicSourceEtaRatFunc phi) :
    HC4.Polynomial.ShiftedPolynomialAutonomousLogODE 0 R phi := by
  let E := HC4.Polynomial.eulerDerivative phi
  let H := HC4.Polynomial.logarithmicEtaNumerator phi
  let m := R.natDegree

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
      Polynomial.aeval (logarithmicSourceRatFunc phi) R =
        logarithmicSourceEtaRatFunc phi *
          Polynomial.aeval (logarithmicSourceRatFunc phi) (1 : Polynomial K) := by
    simpa using hidentity

  have hcleared :=
    clearedPolynomialSubstitution_identity_of_ratFunc
      (K := K)
      (rho := logarithmicSourceRatFunc phi)
      (eta := logarithmicSourceEtaRatFunc phi)
      (A := R) (B := (1 : Polynomial K))
      (N := E) (D := phi) (H := H) (m := m)
      hphi hRho hEta
      (by simp [m]) (by simp [m]) hcross

  rw [clearedPolynomialSubstitution_one] at hcleared
  have hm : 2 ≤ m := by simpa [m] using hdeg
  have hpow : phi ^ m = phi ^ (m - 2) * phi ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hcleared

  have hphi2 : phi ^ 2 ≠ 0 := pow_ne_zero 2 hphi
  have hcancel :
      clearedPolynomialSubstitution m R E phi =
        H * phi ^ (m - 2) := by
    apply mul_right_cancel₀ hphi2
    calc
      clearedPolynomialSubstitution m R E phi * phi ^ 2 =
          H * (phi ^ (m - 2) * phi ^ 2) := hcleared
      _ = (H * phi ^ (m - 2)) * phi ^ 2 := by ring

  unfold HC4.Polynomial.ShiftedPolynomialAutonomousLogODE
  have hrhs :
      HC4.Polynomial.shiftedAutonomousClearedRHS 0 R phi =
        H * phi ^ (m - 2) := by
    rw [shiftedAutonomousClearedRHS_zero_eq_clearedPolynomialSubstitution]
    exact hcancel
  dsimp [H, m] at hrhs ⊢
  rw [HC4.Polynomial.shiftedEtaNumerator_zero]
  exact hrhs.symm

end

end HC4.RationalRigidity