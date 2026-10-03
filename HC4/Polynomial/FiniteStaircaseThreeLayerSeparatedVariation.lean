import HC4.Polynomial.FiniteStaircaseThreeLayerEvaluation
import HC4.Valuation.SeparatedParameterDualJet
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Separated terminal first variation of a three-layer pencil

For a singular three-layer matrix pencil

    M(t) = A + t^r B + t^N C

with

    0 < r < N < 2r,

the determinant coefficient at order `N` cannot contain two positive-order
entry contributions.  It is therefore exactly the first variation from `A`
toward `C`; the intermediate layer `B` is invisible at this order.

The theorem below applies this after longitudinal evaluation, which is the
form needed by the final A19 endpoint-cross contradiction.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K]

/-- Constant/terminal dual-number pencil. -/
noncomputable def terminalFirstVariationDualMatrix
    (A C : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  fun i j => (A i j, C i j)

/-- **Evaluated separated terminal variation vanishes.** -/
theorem snd_det_terminalFirstVariation_eval_eq_zero
    (x : K)
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (r N : ℕ)
    (hr : 0 < r) (hrN : r < N) (hN2r : N < 2 * r)
    (hdet : (parameterThreeLayerMatrix A B C r N).det = 0) :
    TrivSqZeroExt.snd
      (terminalFirstVariationDualMatrix
        (evalPolynomialMatrix x A)
        (evalPolynomialMatrix x C)).det = 0 := by
  let Ae := evalPolynomialMatrix x A
  let Be := evalPolynomialMatrix x B
  let Ce := evalPolynomialMatrix x C
  let M := parameterThreeLayerMatrix Ae Be Ce r N
  have hdetE : M.det = 0 := by
    dsimp [M, Ae, Be, Ce]
    exact det_parameterThreeLayerMatrix_eval_eq_zero x A B C r N hdet
  have hr0 : r ≠ 0 := Nat.ne_of_gt hr
  have hN0 : N ≠ 0 := by omega
  have hNr : N ≠ r := by omega
  have hgap : ∀ i j,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow r (M i j) := by
    intro i j m hmpos hmlt
    have hm0 : m ≠ 0 := Nat.ne_of_gt hmpos
    have hmr : m ≠ r := by omega
    have hmN : m ≠ N := by omega
    simp [M, parameterThreeLayerMatrix, Polynomial.coeff_monomial,
      hm0, hmr, hmN]
  have hjet :
      HC4.Valuation.matrixSeparatedParameterDualJet
          hr hrN hN2r M hgap =
        terminalFirstVariationDualMatrix Ae Ce := by
    apply Matrix.ext
    intro i j
    rw [HC4.Valuation.matrixSeparatedParameterDualJet_apply]
    simp [M, parameterThreeLayerMatrix,
      terminalFirstVariationDualMatrix, Polynomial.coeff_monomial,
      hr0, hN0, hNr]
  have hbridge :=
    HC4.Valuation.snd_det_matrixSeparatedParameterDualJet
      (R := K) hr hrN hN2r M hgap
  have hzero :
      TrivSqZeroExt.snd
        (HC4.Valuation.matrixSeparatedParameterDualJet
          hr hrN hN2r M hgap).det = 0 := by
    rw [hbridge, hdetE]
    simp
  rw [hjet] at hzero
  exact hzero

end

end HC4.Polynomial
