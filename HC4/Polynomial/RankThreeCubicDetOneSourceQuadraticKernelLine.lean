import HC4.Polynomial.RankThreeCubicDetOneSourceOriginBorderedHessian
import Mathlib.Tactic

/-!
# Determinant-one source: a quadratic transverse kernel at the origin is a line

This is a source-level consequence of the actual Hessian determinant
identity. If the true weight-two source transverse Hessian T at
(x=a,y=0) has a specified nonzero kernel vector w, then its whole
kernel is spanned by w.

The same w couples nontrivially to the original longitudinal
mixed Hessian at the origin. Both facts follow from the verified
algebra of invertible bordered 4x4 matrices, after identifying
their original-source transverse block. No artificial Hessian
completion or standalone endpoint assumptions are used.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- If the actual source quadratic transverse block has any
nonzero kernel direction at the origin, then its kernel is
exactly one-dimensional, with that direction spanning it. -/
theorem sourceCubic_detOne_originQuadraticKernel_isLine
    (F : SB K) (a : K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (w0 : Fin 3 → K) (hw0 : w0 ≠ 0)
    (hTker : ∀ i : Fin 3,
      (∑ j : Fin 3,
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
          (referenceSlice a
            (hessian (initialForm transverseCubicWeight 2 F)
              (.inr i) (.inr j)))) * w0 j) = 0) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => ev (hessian L2 (.inr i) (.inr j))
    let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
      ev.mapMatrix (hessian F)
    (∑ j : Fin 3, B0 (.inl ()) (.inr j) * w0 j) ≠ 0 ∧
      (∀ z : Fin 3 → K, T *ᵥ z = 0 →
        ∃ c : K, ∀ j : Fin 3, z j = c * w0 j) := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => ev (hessian L2 (.inr i) (.inr j))
  let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    ev.mapMatrix (hessian F)
  obtain ⟨hdet, hblock⟩ :=
    sourceCubic_detOne_originBordered_transverse_eq_quadratic
      F a hcap hdetOne
  have hBne : B0.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  have hBrows : ∀ i : Fin 3,
      (∑ j : Fin 3, B0 (.inr i) (.inr j) * w0 j) = 0 := by
    intro i
    calc
      (∑ j : Fin 3, B0 (.inr i) (.inr j) * w0 j) =
          ∑ j : Fin 3, T i j * w0 j := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (fun x : K => x * w0 j) (hblock i j)
      _ = 0 := hTker i
  have hcoupling :=
    borderedInvertible_transverseKernel_longitudinalPairing_ne_zero
      B0 hBne w0 hw0 hBrows
  refine ⟨hcoupling, ?_⟩
  intro z hz
  apply borderedInvertible_transverseKernel_isLine
    B0 hBne w0 hw0 hBrows z
  intro i
  have hi := congrFun hz i
  have hTz : (∑ j : Fin 3, T i j * z j) = 0 := by
    simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hi
  calc
    (∑ j : Fin 3, B0 (.inr i) (.inr j) * z j) =
        ∑ j : Fin 3, T i j * z j := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun x : K => x * z j) (hblock i j)
    _ = 0 := hTz

end
end HC4.Polynomial.RankThreeCubic
