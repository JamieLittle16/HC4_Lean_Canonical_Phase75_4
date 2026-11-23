import HC4.Valuation.QuadraticTransverseCapSourceTransverseGradient
import Mathlib.Tactic

/-!
# Fixed-longitudinal-coordinate transverse gradients are bijective

A concrete source-level result for ALL regular quadratic-cap
determinant-one potentials, not an abstract matrix model.

For every x in K, the actual map
   y ↦ (∂F/∂y_1, ∂F/∂y_2, ∂F/∂y_3)(x,y)
is a bijection of K^3, with an explicit inverse formed from the
source's polynomial inverse transverse Hessian.

This is the genuine transverse-fibre half of the global gradient
automorphism theorem. The longitudinal slope is still to be proved.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- For the original source of transverse degree at most two and
full Hessian determinant one, every longitudinal fibre of the
transverse gradient is bijective if the transverse Hessian has
nonzero determinant as a polynomial in x.

This conclusion is about the ACTUAL evaluated pderiv of F. -/
theorem quadraticTransverseCapSource_regularTransverseFibre_bijective
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (x : K) :
    Function.Bijective
      (fun y : Fin 3 → K =>
        fun i : Fin 3 =>
          MvPolynomial.eval (Fin.cons x y)
            (MvPolynomial.pderiv i.succ F)) := by
  classical
  obtain ⟨P, hCP, hPC, _hd⟩ :=
    quadraticTransverseCapSource_regularPolynomialInverse
      F hcap hdet hregular
  let ev : Polynomial K →+* K := Polynomial.evalRingHom x
  let C : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    (quadraticTransverseCapSourceAxisThreeBlock F).matrix
  let Cx : Matrix (Fin 3) (Fin 3) K := C.map ev
  let Px : Matrix (Fin 3) (Fin 3) K := P.map ev
  let bx : Fin 3 → K :=
    fun i => Polynomial.eval x
      (quadraticTransverseCapSourceLinearCoefficients F i)
  have hCPx : Cx * Px = 1 := by
    change (C.map ev) * (P.map ev) = 1
    rw [← Matrix.map_mul, hCP]
    simp
  have hPCx : Px * Cx = 1 := by
    change (P.map ev) * (C.map ev) = 1
    rw [← Matrix.map_mul, hPC]
    simp
  let G : (Fin 3 → K) → (Fin 3 → K) :=
    fun y => bx + Cx *ᵥ y
  let J : (Fin 3 → K) → (Fin 3 → K) :=
    fun p => Px *ᵥ (p - bx)
  have hleft : Function.LeftInverse J G := by
    intro y
    change Px *ᵥ (bx + Cx *ᵥ y - bx) = y
    have hsub : bx + Cx *ᵥ y - bx = Cx *ᵥ y := by abel
    rw [hsub, ← Matrix.mulVec_mulVec, hPCx, Matrix.one_mulVec]
  have hright : Function.RightInverse J G := by
    intro p
    change bx + Cx *ᵥ (Px *ᵥ (p - bx)) = p
    rw [← Matrix.mulVec_mulVec, hCPx, Matrix.one_mulVec]
    abel
  have hG : Function.Bijective G :=
    ⟨hleft.injective, hright.surjective⟩
  have hactual :
      (fun y : Fin 3 → K =>
        fun i : Fin 3 =>
          MvPolynomial.eval (Fin.cons x y)
            (MvPolynomial.pderiv i.succ F)) = G := by
    funext y i
    have hf := quadraticTransverseCapSource_transverseGradient_affine
      F hcap x y i
    simpa [G, bx, Cx, C, ev, Matrix.mulVec, dotProduct] using hf
  rw [hactual]
  exact hG

end

end HC4.Valuation
