import HC4.Polynomial.RankThreeCubicDetOneBorderedKernelLine
import Mathlib.Tactic

/-!
# Original det-one source Hessian at the transverse origin

Let F be the actual source polynomial of transverse weight at
most three. At the original longitudinal anchor x=a and
transverse origin y=0, evaluate all entries of Hess(F).

The weight-three transverse Hessian entries are homogeneous
linear in y and vanish at the origin. The remainder below
weight two has identically zero transverse Hessian.

Consequently the transverse 3-by-3 block of the ORIGINAL
specialized Hessian is exactly the transverse Hessian of
the TRUE weight-two source layer at (a,0).

The original det-one identity remains det(B0)=1 after this
evaluation, so this is a source-derived invertible bordered
matrix, not an abstract completion.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- The original Hessian at (a,0) has determinant one and
its transverse block equals the original quadratic
transverse Hessian at that same point. -/
theorem sourceCubic_detOne_originBordered_transverse_eq_quadratic
    (F : SB K) (a : K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1) :
    let L2 : SB K := initialForm transverseCubicWeight 2 F
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
      ev.mapMatrix (hessian F)
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => ev (hessian L2 (.inr i) (.inr j))
    B0.det = 1 ∧
      (∀ i j : Fin 3, B0 (.inr i) (.inr j) = T i j) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    ev.mapMatrix (hessian F)
  let T : Matrix (Fin 3) (Fin 3) K :=
    fun i j => ev (hessian L2 (.inr i) (.inr j))
  have hdet : B0.det = 1 := by
    calc
      B0.det = ev (hessian F).det := by
        exact (RingHom.map_det ev (hessian F)).symm
      _ = 1 := by
        change ev (hessianDeterminant F) = 1
        rw [hdetOne]
        simp
  have hL3 (i j : Fin 3) :
      ev (hessian L3 (.inr i) (.inr j)) = 0 := by
    have hhom :=
      sourceCubic_transverseHessian_homogeneous_one a F i j
    have hz :=
      homogeneous_positive_origin_zero
        (sourceTransverseHessian a L3 i j) 0 hhom
    simpa only [sourceTransverseHessian, hessian_apply] using hz
  have hRlow (i j : Fin 3) :
      ev (hessian Rlow (.inr i) (.inr j)) = 0 := by
    have hz := sourceCubic_belowTwo_transverseHessian_zero F hcap i j
    rw [sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F] at hz
    rw [hz]
    simp
  refine ⟨hdet, ?_⟩
  intro i j
  change ev (hessian F (.inr i) (.inr j)) =
    ev (hessian L2 (.inr i) (.inr j))
  have hh :=
    congrFun (congrFun (sourceCubic_hessian_three_two_lower_decomposition F)
      (.inr i)) (.inr j)
  rw [hh, map_add, map_add, hL3 i j, hRlow i j]
  ring

end
end HC4.Polynomial.RankThreeCubic
