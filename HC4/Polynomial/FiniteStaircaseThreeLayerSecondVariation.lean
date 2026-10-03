import HC4.Polynomial.FiniteStaircaseSecondVariationTopCoefficient
import HC4.Valuation.ParameterGapSecondJet
import Mathlib.Tactic

/-!
# Three-layer singular pencils force the top second variation to vanish

This is the generic determinant bridge used by the final A19 one-fibre
elimination.  Let

    M(t) = A + t^q B + t^N C,    0 < q < N.

If `det M = 0`, then the second parameter-gap jet at order `q` has zero
determinant.  At the top longitudinal degree, an arbitrary degree-one
coefficient at order `2q` cannot contribute; hence the pure `A/B` second
variation top determinant vanishes.

No HC4 state occurs here.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {R : Type u} [CommRing R]

/-- A literal three-layer matrix polynomial in an outer parameter. -/
noncomputable def parameterThreeLayerMatrix
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (q N : ℕ) : Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial R)) :=
  fun i j =>
    Polynomial.C (A i j) +
      Polynomial.monomial q (B i j) +
      Polynomial.monomial N (C i j)

/-- **Generic three-layer second-variation vanishing.**

The conclusion is independent of whether the terminal layer happens to occur
at order `2q`: if it does, its longitudinal degree is at most one and the top
coefficient theorem removes it automatically. -/
theorem snd_snd_det_secondVariationTopMatrix_eq_zero_of_threeLayer_det_zero
    (A B C : Matrix (Fin 4) (Fin 4) (Polynomial R))
    (q N m : ℕ)
    (hq : 0 < q) (hqN : q < N) (hm : 1 < m)
    (hdet : (parameterThreeLayerMatrix A B C q N).det = 0)
    (hA : ∀ i j, (A i j).natDegree ≤ 1)
    (hB : ∀ i j, (B i j).natDegree ≤ m)
    (hC : ∀ i j, (C i j).natDegree ≤ 1) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd (secondVariationTopMatrix A B m).det) = 0 := by
  let M := parameterThreeLayerMatrix A B C q N
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
  let C₂ : Matrix (Fin 4) (Fin 4) (Polynomial R) :=
    if N = 2 * q then C else 0
  have hC₂ : ∀ i j, (C₂ i j).natDegree ≤ 1 := by
    intro i j
    by_cases hres : N = 2 * q
    · simp [C₂, hres, hC i j]
    · simp [C₂, hres]
  have hjet :
      HC4.Valuation.matrixParameterGapSecondJet hq M hgap =
        secondVariationJetMatrix A B C₂ := by
    apply Matrix.ext
    intro i j
    rw [HC4.Valuation.matrixParameterGapSecondJet_apply]
    by_cases hres : N = 2 * q
    · subst N
      simp [M, parameterThreeLayerMatrix, C₂,
        secondVariationJetMatrix, secondVariationJetEntry,
        Polynomial.coeff_monomial, hq0, h2q0, h2qq]
    · simp [M, parameterThreeLayerMatrix, C₂,
        secondVariationJetMatrix, secondVariationJetEntry,
        Polynomial.coeff_monomial, hq0, hN0, hNq,
        h2q0, h2qq, hres]
  have hbridge :=
    HC4.Valuation.snd_snd_det_matrixParameterGapSecondJet
      (R := Polynomial R) hq M hgap
  have hjetZero :
      TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (HC4.Valuation.matrixParameterGapSecondJet hq M hgap).det) = 0 := by
    rw [hbridge, show M.det = 0 by simpa [M] using hdet]
    simp
  rw [hjet] at hjetZero
  have htop := coeff_top_snd_snd_det_secondVariationJetMatrix
    A B C₂ m hm hA hB hC₂
  have hcoeffZero :
      (TrivSqZeroExt.snd
        (TrivSqZeroExt.snd
          (secondVariationJetMatrix A B C₂).det)).coeff (2 + 2 * m) = 0 := by
    rw [hjetZero]
    simp
  rw [htop] at hcoeffZero
  exact hcoeffZero

end

end HC4.Polynomial
