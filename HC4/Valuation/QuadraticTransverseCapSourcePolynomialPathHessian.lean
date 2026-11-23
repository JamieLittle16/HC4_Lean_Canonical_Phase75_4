import HC4.Valuation.QuadraticTransverseCapPolynomialSectionChainRule
import Mathlib.Tactic

/-!
# Actual source transverse Hessian along arbitrary polynomial fibres

For a genuinely quadratic-transverse source, all three-by-three
transverse Hessian entries are independent of the transverse
coordinates, and stay equal to the source-axis matrix C(X) after
substituting ANY polynomial transverse curve y(X).

The lemmas in this file make that equality at the level of
polynomial substitution, not just at selected scalar points.
Together with the source polynomial chain rule, this is exactly
what is needed to differentiate the constant transverse-gradient
fibre in K[X].
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluating a polynomial path substitution at t is the same
as evaluating the original source at the point q(t). -/
theorem sourcePolynomialPathSubstitution_eval
    (Q : MvPolynomial (Fin 4) K)
    (q : Fin 4 → Polynomial K)
    (t : K) :
    Polynomial.eval t (sourcePolynomialPathSubstitution q Q) =
      MvPolynomial.eval (fun i => Polynomial.eval t (q i)) Q := by
  let L : MvPolynomial (Fin 4) K →+* K :=
    (Polynomial.evalRingHom t).comp
      (sourcePolynomialPathSubstitution q).toRingHom
  let R : MvPolynomial (Fin 4) K →+* K :=
    MvPolynomial.eval (fun i => Polynomial.eval t (q i))
  have h : L = R := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [L, R, sourcePolynomialPathSubstitution]
    · intro i
      simp [L, R, sourcePolynomialPathSubstitution]
  exact congrArg (fun e : MvPolynomial (Fin 4) K →+* K => e Q) h

/-- A genuine source transverse Hessian entry stays equal to its
longitudinal-axis restriction on ANY polynomial curve y(X).
The proof uses only the whole-source cap-two hypothesis and the
already-proved global affine-evaluation identity. -/
theorem quadraticTransverseCapSource_polynomialPath_transverseHessian
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (y : Fin 3 → Polynomial K)
    (i j : Fin 3) :
    sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
        (HC4.Polynomial.hessian F i.succ j.succ) =
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix i j := by
  classical
  let H := HC4.Polynomial.hessian F i.succ j.succ
  have hflat (k : Fin 3) :
      MvPolynomial.pderiv k.succ H = 0 := by
    change MvPolynomial.pderiv k.succ
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ F)) = 0
    exact quadraticTransverseCap_two_tripleTransversePderiv_zero
      F hcap i j k
  have hsecond : ∀ k l : Fin 3,
      MvPolynomial.pderiv l.succ
        (MvPolynomial.pderiv k.succ H) = 0 := by
    intro k l
    rw [hflat k]
    simp
  apply Polynomial.funext
  intro t
  have hpoint :
      (fun a : Fin 4 =>
        Polynomial.eval t ((Fin.cons Polynomial.X y) a)) =
          Fin.cons t (fun j : Fin 3 => Polynomial.eval t (y j)) := by
    funext a
    cases a using Fin.cases with
    | zero => simp
    | succ k => rfl
  have heval := eval_affine_transverse_of_second_pderivs_zero
    H hsecond t (fun k => Polynomial.eval t (y k))
  have heval0 :
      MvPolynomial.eval
          (Fin.cons t (fun k : Fin 3 => Polynomial.eval t (y k))) H =
        MvPolynomial.eval
          (Fin.cons t (fun _ : Fin 3 => (0 : K))) H := by
    simpa [hflat] using heval
  calc
    Polynomial.eval t
        (sourcePolynomialPathSubstitution
          (Fin.cons Polynomial.X y)
          (HC4.Polynomial.hessian F i.succ j.succ)) =
      MvPolynomial.eval
        (fun a : Fin 4 =>
          Polynomial.eval t ((Fin.cons Polynomial.X y) a)) H :=
        sourcePolynomialPathSubstitution_eval H
          (Fin.cons Polynomial.X y) t
    _ = MvPolynomial.eval
        (Fin.cons t (fun _ : Fin 3 => (0 : K))) H := by
          rw [hpoint, heval0]
    _ = Polynomial.eval t
        (longitudinalAxisRestrictionRingHom (K := K) H) := by
          exact (eval_finCons_zero_eq_longitudinalAxisRestriction H t).trans
            (congrArg (Polynomial.eval t)
              (longitudinalAxisRestrictionRingHom_apply H).symm)
    _ = Polynomial.eval t
        ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) := by
          exact congrArg (Polynomial.eval t)
            (quadraticTransverseCapSource_axisThreeBlock_entry F i j)

end

end HC4.Valuation
