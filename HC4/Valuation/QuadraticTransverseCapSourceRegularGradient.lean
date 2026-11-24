import HC4.Valuation.QuadraticTransverseCapSourceRegularSlope
import HC4.Newton.TerminalCollision
import Mathlib.Tactic

/-!
# Full gradient bijectivity of the original regular quadratic-cap source

For every characteristic-zero field, a four-variable source F of
transverse degree at most two, with Hessian determinant one and
nonzero transverse Hessian determinant, has a bijective actual
evaluated gradient. All fibre and longitudinal drift equations are
derived internally from F.

This is the regular-branch endpoint, not a conditional fibre lemma.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- Actual gradient bijectivity for the regular transverse Hessian
branch of the original four-variable quadratic-cap potential. -/
theorem quadraticTransverseCapSource_regularGradient_bijective
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0) :
    Function.Bijective (mvGradientMap F) := by
  classical
  obtain ⟨d, hdn, hfibres⟩ :=
    quadraticTransverseCapSource_regularAffineFibre F hcap hdet hregular
  have hsolve (out : Fin 4 → K) :
      ∃ z : Fin 4 → K, mvGradientMap F z = out ∧
        ∀ w : Fin 4 → K, mvGradientMap F w = out → w = z := by
    let p : Fin 3 → K := fun i => out i.succ
    obtain ⟨y, k, hgrad, hlong⟩ := hfibres p
    let q : Fin 4 → Polynomial K := Fin.cons (Polynomial.X : Polynomial K) y
    let path : K → (Fin 4 → K) :=
      fun t => Fin.cons t (fun i : Fin 3 => Polynomial.eval t (y i))
    have hpoint (t : K) :
        (fun a : Fin 4 => Polynomial.eval t (q a)) = path t := by
      funext a
      cases a using Fin.cases with
      | zero => simp [q, path]
      | succ i => rfl
    have htrans (t : K) (i : Fin 3) :
        mvGradientMap F (path t) i.succ = p i := by
      have hi := congrArg (Polynomial.eval t) (hgrad i)
      change Polynomial.eval t (sourcePolynomialPathSubstitution q
        (MvPolynomial.pderiv i.succ F)) =
          Polynomial.eval t (Polynomial.C (p i)) at hi
      rw [sourcePolynomialPathSubstitution_eval, hpoint, Polynomial.eval_C] at hi
      exact hi
    have hlinear (t : K) :
        mvGradientMap F (path t) 0 = d⁻¹ * t + k := by
      have hi := congrArg (Polynomial.eval t) hlong
      change Polynomial.eval t (sourcePolynomialPathSubstitution q
        (MvPolynomial.pderiv (0 : Fin 4) F)) =
          Polynomial.eval t (Polynomial.C d⁻¹ * Polynomial.X + Polynomial.C k) at hi
      rw [sourcePolynomialPathSubstitution_eval, hpoint] at hi
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X] using hi
    let x : K := d * (out 0 - k)
    have hx : d⁻¹ * x + k = out 0 := by
      calc
        d⁻¹ * x + k = (d⁻¹ * d) * (out 0 - k) + k := by dsimp [x]; ring
        _ = out 0 := by rw [inv_mul_cancel₀ hdn, one_mul]; ring
    refine ⟨path x, ?_, ?_⟩
    · funext i
      cases i using Fin.cases with
      | zero => exact (hlinear x).trans hx
      | succ j => exact htrans x j
    · intro w hw
      have hwpoint :
          Fin.cons (w 0) (fun i : Fin 3 => w i.succ) = w := by
        funext i
        cases i using Fin.cases <;> rfl
      have htail : (fun i : Fin 3 => w i.succ) =
          (fun i : Fin 3 => Polynomial.eval (w 0) (y i)) := by
        apply (quadraticTransverseCapSource_regularTransverseFibre_bijective
          F hcap hdet hregular (w 0)).injective
        funext i
        change MvPolynomial.eval
          (Fin.cons (w 0) (fun j : Fin 3 => w j.succ))
            (MvPolynomial.pderiv i.succ F) =
          MvPolynomial.eval (path (w 0)) (MvPolynomial.pderiv i.succ F)
        rw [hwpoint]
        exact (congrFun hw i.succ).trans (htrans (w 0) i).symm
      have hwpath : w = path (w 0) := by
        funext a
        cases a using Fin.cases with
        | zero => rfl
        | succ i => exact congrFun htail i
      have hwlong : d⁻¹ * w 0 + k = out 0 := by
        calc
          d⁻¹ * w 0 + k = mvGradientMap F (path (w 0)) 0 :=
            (hlinear (w 0)).symm
          _ = mvGradientMap F w 0 :=
            congrArg (fun z : Fin 4 → K => mvGradientMap F z 0) hwpath.symm
          _ = out 0 := congrFun hw 0
      have hxeq : w 0 = x := by
        apply mul_left_cancel₀ (inv_ne_zero hdn)
        exact add_right_cancel (hwlong.trans hx.symm)
      exact hwpath.trans (congrArg path hxeq)
  constructor
  · intro a b hab
    obtain ⟨z, hz, huniq⟩ := hsolve (mvGradientMap F b)
    exact (huniq a hab).trans (huniq b rfl).symm
  · intro out
    obtain ⟨z, hz, _⟩ := hsolve out
    exact ⟨z, hz⟩

end

end HC4.Valuation
