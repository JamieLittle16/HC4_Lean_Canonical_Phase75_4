import HC4.Polynomial.FiniteStaircaseThreeLayerSecondVariation
import Mathlib.Tactic

/-!
# Evaluation bridge for three-layer matrix pencils

Evaluating the longitudinal coefficient polynomials of an exact three-layer
parameter pencil is a ring homomorphism.  Hence determinant zero is preserved,
and the resulting evaluated pencil has the same three parameter orders.
This lets the final A19 central calculation use constant moment matrices.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K]

/-- Entrywise evaluation of a polynomial matrix. -/
noncomputable def evalPolynomialMatrix
    (x : K) (M : Matrix (Fin 4) (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i j => Polynomial.eval x (M i j)

/-- Mapping the outer parameter polynomial by longitudinal evaluation turns a
three-layer polynomial-coefficient pencil into the three-layer evaluated
matrix pencil. -/
theorem map_parameterThreeLayerMatrix_eval
    (x : K)
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (q N : ℕ) :
    (Polynomial.mapRingHom (Polynomial.evalRingHom x)).mapMatrix
        (parameterThreeLayerMatrix A B C q N) =
      parameterThreeLayerMatrix
        (evalPolynomialMatrix x A)
        (evalPolynomialMatrix x B)
        (evalPolynomialMatrix x C) q N := by
  apply Matrix.ext
  intro i j
  simp [parameterThreeLayerMatrix, evalPolynomialMatrix]

/-- Determinant zero survives longitudinal evaluation of a three-layer pencil. -/
theorem det_parameterThreeLayerMatrix_eval_eq_zero
    (x : K)
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (q N : ℕ)
    (hdet : (parameterThreeLayerMatrix A B C q N).det = 0) :
    (parameterThreeLayerMatrix
      (evalPolynomialMatrix x A)
      (evalPolynomialMatrix x B)
      (evalPolynomialMatrix x C) q N).det = 0 := by
  let ev : Polynomial (Polynomial K) →+* Polynomial K :=
    Polynomial.mapRingHom (Polynomial.evalRingHom x)
  have hm := congrArg ev hdet
  have hmap :
      ev.mapMatrix (parameterThreeLayerMatrix A B C q N) =
        parameterThreeLayerMatrix
          (evalPolynomialMatrix x A)
          (evalPolynomialMatrix x B)
          (evalPolynomialMatrix x C) q N := by
    simpa [ev] using map_parameterThreeLayerMatrix_eval x A B C q N
  have hdetMap :
      (ev.mapMatrix (parameterThreeLayerMatrix A B C q N)).det = 0 := by
    rw [← RingHom.map_det]
    simpa [ev] using hm
  rw [hmap] at hdetMap
  exact hdetMap

/-- **Evaluated nonresonant second variation vanishes.**  If the terminal
parameter order is not twice the first positive order, the exact second jet
contains no terminal correction, so the evaluated endpoint/interior second
variation has zero determinant component. -/
theorem snd_snd_det_secondVariationJetMatrix_eval_eq_zero
    (x : K)
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial K))
    (q N : ℕ)
    (hq : 0 < q) (hqN : q < N) (hres : N ≠ 2 * q)
    (hdet : (parameterThreeLayerMatrix A B C q N).det = 0) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd
        (secondVariationJetMatrix
          (evalPolynomialMatrix x A)
          (evalPolynomialMatrix x B) 0).det) = 0 := by
  let Ae := evalPolynomialMatrix x A
  let Be := evalPolynomialMatrix x B
  let Ce := evalPolynomialMatrix x C
  let M := parameterThreeLayerMatrix Ae Be Ce q N
  have hdetE : M.det = 0 := by
    dsimp [M, Ae, Be, Ce]
    exact det_parameterThreeLayerMatrix_eval_eq_zero x A B C q N hdet
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hN0 : N ≠ 0 := by omega
  have hNq : N ≠ q := by omega
  have h2q0 : 2 * q ≠ 0 := by omega
  have h2qq : 2 * q ≠ q := by omega
  have hgap : ∀ i j,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow q (M i j) := by
    intro i j r hrpos hrlt
    have hr0 : r ≠ 0 := Nat.ne_of_gt hrpos
    have hrq : r ≠ q := by omega
    have hrN : r ≠ N := by omega
    simp [M, parameterThreeLayerMatrix, Polynomial.coeff_monomial,
      hr0, hrq, hrN]
  have hjet :
      HC4.Valuation.matrixParameterGapSecondJet hq M hgap =
        secondVariationJetMatrix Ae Be 0 := by
    apply Matrix.ext
    intro i j
    rw [HC4.Valuation.matrixParameterGapSecondJet_apply]
    simp [M, parameterThreeLayerMatrix, secondVariationJetMatrix,
      secondVariationJetEntry, Polynomial.coeff_monomial,
      hq0, hN0, hNq, h2q0, h2qq, hres]
  have hbridge :=
    HC4.Valuation.snd_snd_det_matrixParameterGapSecondJet
      (R := K) hq M hgap
  have hzero :
      TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (HC4.Valuation.matrixParameterGapSecondJet hq M hgap).det) = 0 := by
    rw [hbridge, hdetE]
    simp
  rw [hjet] at hzero
  exact hzero

end

end HC4.Polynomial
