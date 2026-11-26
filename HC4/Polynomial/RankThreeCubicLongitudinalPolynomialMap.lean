module

public import HC4.Polynomial.RankThreeCubicPoleQuadraticTransport
public import Mathlib.Tactic

/-!
# Base-field polynomial substitution commutes with fraction-field embedding

Once cubic third derivatives have been represented as one-variable
polynomials, their longitudinal evaluation at a+t is defined in K[t].
This general lemma verifies that embedding that polynomial in the
fraction field agrees exactly with substitution there.

This avoids inventing a local integrality hypothesis at a pole:
the polynomial time coefficients originate in the *ground field*.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open _root_.Polynomial

noncomputable section

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

/-- Evaluating a one-variable source polynomial at a+t and then
extending coefficients from K to F is the same as first extending
scalars and then evaluating at a+t. -/
theorem longitudinalPolynomial_eval_map
    (a : K) (T : MvPolynomial Unit K) :
    (_root_.Polynomial.mapRingHom (algebraMap K F))
        (MvPolynomial.aeval
          (fun _ : Unit => _root_.Polynomial.C a + _root_.Polynomial.X) T) =
      MvPolynomial.aeval
        (fun _ : Unit =>
          _root_.Polynomial.C (algebraMap K F a) + _root_.Polynomial.X) T := by
  classical
  induction T using MvPolynomial.induction_on with
  | C c =>
      simp [MvPolynomial.aeval_C, _root_.Polynomial.mapRingHom,
        IsScalarTower.algebraMap_apply K F (_root_.Polynomial F)]
  | add p q hp hq =>
      simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X]
      rw [hp]
      have hX :
          (_root_.Polynomial.mapRingHom (algebraMap K F))
            (_root_.Polynomial.C a + _root_.Polynomial.X) =
              _root_.Polynomial.C (algebraMap K F a) +
                _root_.Polynomial.X := by simp
      rw [hX]

end
end HC4.Polynomial.RankThreeCubic
