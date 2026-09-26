import HC4.Polynomial.FiniteStaircaseThreeLayerSecondVariation
import HC4.Valuation.ParameterGapIntermediateDualJet
import Mathlib.Tactic

/-!
# Intermediate first variation of a three-layer pencil

For

    M(t) = A + t^q B + t^N C,   0 < q < N < 2q,

the coefficient at order `N` in the determinant cannot contain the middle
layer: two positive contributions would already have order at least `2q`.
Thus determinant zero forces the ordinary first variation from `A` toward
`C` to vanish.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {R : Type u} [CommRing R]

/-- Ordinary endpoint dual pencil. -/
noncomputable def endpointDualPencil
    (A C : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) (DualNumber R) :=
  fun i j => (A i j, C i j)

/-- **Intermediate endpoint variation vanishes in a singular three-layer
pencil.** -/
theorem snd_det_endpointDualPencil_eq_zero_of_threeLayer_det_zero
    (A B C : Matrix (Fin 4) (Fin 4) R)
    (q N : ℕ)
    (hq : 0 < q) (hqN : q < N) (hN2q : N < 2 * q)
    (hdet : (parameterThreeLayerMatrix
      (R := R) (fun i j => Polynomial.C (A i j))
      (fun i j => Polynomial.C (B i j))
      (fun i j => Polynomial.C (C i j)) q N).det = 0) :
    TrivSqZeroExt.snd (endpointDualPencil A C).det = 0 := by
  let M := parameterThreeLayerMatrix
    (R := R) (fun i j => Polynomial.C (A i j))
    (fun i j => Polynomial.C (B i j))
    (fun i j => Polynomial.C (C i j)) q N
  have hgap : ∀ i j,
      HC4.Valuation.HasNoPositiveParameterCoeffBelow q (M i j) := by
    intro i j r hrpos hrlt
    have hr0 : r ≠ 0 := Nat.ne_of_gt hrpos
    have hrq : r ≠ q := by omega
    have hrN : r ≠ N := by omega
    simp [M, parameterThreeLayerMatrix, Polynomial.coeff_monomial,
      hr0, hrq, hrN]
  have hjet :
      HC4.Valuation.matrixParameterGapIntermediateDualJet
        hq hqN hN2q M hgap = endpointDualPencil A C := by
    apply Matrix.ext
    intro i j
    rw [HC4.Valuation.matrixParameterGapIntermediateDualJet_apply]
    simp [M, parameterThreeLayerMatrix, endpointDualPencil,
      Polynomial.coeff_monomial, Nat.ne_of_gt hq,
      show N ≠ 0 by omega, show N ≠ q by omega]
  have hbridge :=
    HC4.Valuation.snd_det_matrixParameterGapIntermediateDualJet
      (R := R) hq hqN hN2q M hgap
  have hzeroCoeff : M.det.coeff N = 0 := by
    rw [show M.det = 0 by simpa [M] using hdet]
    simp
  rw [hjet] at hbridge
  rw [hzeroCoeff] at hbridge
  exact hbridge

end

end HC4.Polynomial
