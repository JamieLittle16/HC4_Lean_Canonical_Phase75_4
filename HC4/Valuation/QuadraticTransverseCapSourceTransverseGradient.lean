import HC4.Valuation.QuadraticTransverseCapSourceRegularAffineInverse
import HC4.Valuation.QuadraticTransverseCapAffineSection
import Mathlib.Tactic

/-!
# The actual quadratic-cap transverse gradient is globally affine

For the original four-variable source with transverse degree at most
two, the transverse gradient at every (x,y) is exactly

    grad_y F(x,y) = b(x) + C(x)y,

where b(x) is its genuine axis transverse-linear coefficient vector
and C(x) is its genuine axis transverse Hessian matrix.

No abstract substitute potential or assumed gradient profile is
used. This is the exact source-to-fibre identification required for
the regular-branch polynomial inverse construction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 2048

variable {K : Type*} [Field K] [CharZero K]

/-- Interpolate the transverse coordinates from zero to y in
their canonical index order. n=0 is the axis; n=3 is (x,y). -/
private def transverseStagePoint
    (x : K) (y : Fin 3 → K) (n : ℕ) : Fin 4 → K :=
  Fin.cons x (fun j => if j.val < n then y j else 0)

private theorem stagePoint_agree_off
    (x : K) (y : Fin 3 → K)
    (n : ℕ) (hn : n < 3)
    (j : Fin 4) (hj : j ≠ (⟨n, hn⟩ : Fin 3).succ) :
    transverseStagePoint x y n j =
      transverseStagePoint x y (n + 1) j := by
  cases j using Fin.cases with
  | zero => rfl
  | succ k =>
      change (if k.val < n then y k else 0) =
        (if k.val < n + 1 then y k else 0)
      have hk : k.val ≠ n := by
        intro hh
        apply hj
        exact congrArg Fin.succ (Fin.ext hh)
      by_cases hlt : k.val < n
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · have hnlt : ¬ k.val < n + 1 := by omega
        simp [hlt, hnlt]

/-- If all transverse first partials of P vanish, P has the same
evaluation at (x,y) as at (x,0), for every intermediate stage. -/
private theorem eval_transverseStage_eq_axis
    (P : MvPolynomial (Fin 4) K)
    (hflat : ∀ j : Fin 3, MvPolynomial.pderiv j.succ P = 0)
    (x : K) (y : Fin 3 → K) (n : ℕ) (hn : n ≤ 3) :
    MvPolynomial.eval (transverseStagePoint x y n) P =
      MvPolynomial.eval (transverseStagePoint x y 0) P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < 3 := by omega
      let j : Fin 3 := ⟨n, hlt⟩
      have hstep :
          MvPolynomial.eval (transverseStagePoint x y n) P =
            MvPolynomial.eval (transverseStagePoint x y (n+1)) P :=
        HC4.Newton.eval_eq_of_pderiv_eq_zero
          j.succ P (hflat j)
          (transverseStagePoint x y n)
          (transverseStagePoint x y (n+1))
          (stagePoint_agree_off x y n hlt)
      calc
        MvPolynomial.eval (transverseStagePoint x y (n + 1)) P =
            MvPolynomial.eval (transverseStagePoint x y n) P :=
          hstep.symm
        _ = MvPolynomial.eval (transverseStagePoint x y 0) P :=
          ih (by omega)

/-- A polynomial with all *second transverse* partial derivatives
zero has a globally affine evaluation in the three transverse
coordinates, not just on three test lines. -/
theorem eval_affine_transverse_of_second_pderivs_zero
    (P : MvPolynomial (Fin 4) K)
    (hsecond : ∀ j k : Fin 3,
      MvPolynomial.pderiv k.succ
        (MvPolynomial.pderiv j.succ P) = 0)
    (x : K) (y : Fin 3 → K) :
    MvPolynomial.eval (Fin.cons x y) P =
      MvPolynomial.eval
          (Fin.cons x (fun _ : Fin 3 => (0 : K))) P +
        ∑ j : Fin 3, y j *
          MvPolynomial.eval
            (Fin.cons x (fun _ : Fin 3 => (0 : K)))
            (MvPolynomial.pderiv j.succ P) := by
  classical
  let stage := transverseStagePoint x y
  have hbegin :
      stage 0 = Fin.cons x (fun _ : Fin 3 => (0 : K)) := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ k => simp [stage, transverseStagePoint]
  have hend : stage 3 = Fin.cons x y := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ k => simp [stage, transverseStagePoint, k.isLt]
  have hstep (j : Fin 3) :
      MvPolynomial.eval (stage (j.val+1)) P =
        MvPolynomial.eval (stage j.val) P +
          y j * MvPolynomial.eval (stage 0)
            (MvPolynomial.pderiv j.succ P) := by
    have hj0 : stage j.val j.succ = 0 := by
      simp [stage, transverseStagePoint]
    have hj1 : stage (j.val+1) j.succ = y j := by
      simp [stage, transverseStagePoint]
    have hraw := mvPolynomial_eval_affine_of_secondPderiv_zero
      P j.succ (hsecond j j) (stage j.val)
        (stage (j.val+1)) hj0
        (stagePoint_agree_off x y j.val j.isLt)
    have hflat : ∀ k : Fin 3,
        MvPolynomial.pderiv k.succ
          (MvPolynomial.pderiv j.succ P) = 0 :=
      hsecond j
    have hcoeff := eval_transverseStage_eq_axis
      (MvPolynomial.pderiv j.succ P) hflat
      x y j.val (Nat.le_of_lt j.isLt)
    calc
      MvPolynomial.eval (stage (j.val+1)) P =
          MvPolynomial.eval (stage j.val) P +
            stage (j.val+1) j.succ *
              MvPolynomial.eval (stage j.val)
                (MvPolynomial.pderiv j.succ P) := hraw
      _ = MvPolynomial.eval (stage j.val) P +
            y j * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv j.succ P) := by
        rw [hj1, hcoeff]
  have h0 := hstep (0 : Fin 3)
  have h1 := hstep (1 : Fin 3)
  have h2 := hstep (2 : Fin 3)
  have h0' :
      MvPolynomial.eval (stage 1) P =
        MvPolynomial.eval (stage 0) P +
          y 0 * MvPolynomial.eval (stage 0)
            (MvPolynomial.pderiv (0 : Fin 3).succ P) := by
    simpa using h0
  have h1' :
      MvPolynomial.eval (stage 2) P =
        MvPolynomial.eval (stage 1) P +
          y 1 * MvPolynomial.eval (stage 0)
            (MvPolynomial.pderiv (1 : Fin 3).succ P) := by
    simpa using h1
  have hstage :
      MvPolynomial.eval (stage 3) P =
        MvPolynomial.eval (stage 0) P +
          ∑ j : Fin 3, y j *
            MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv j.succ P) := by
    simp only [Fin.sum_univ_three]
    calc
      MvPolynomial.eval (stage 3) P =
          MvPolynomial.eval (stage 2) P +
            y 2 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (2 : Fin 3).succ P) := h2
      _ = MvPolynomial.eval (stage 1) P +
            y 1 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (1 : Fin 3).succ P) +
            y 2 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (2 : Fin 3).succ P) := by
        rw [h1']
      _ = MvPolynomial.eval (stage 0) P +
            y 0 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (0 : Fin 3).succ P) +
            y 1 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (1 : Fin 3).succ P) +
            y 2 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (2 : Fin 3).succ P) := by
        rw [h0']
      _ = MvPolynomial.eval (stage 0) P +
            (y 0 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (0 : Fin 3).succ P) +
             y 1 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (1 : Fin 3).succ P) +
             y 2 * MvPolynomial.eval (stage 0)
              (MvPolynomial.pderiv (2 : Fin 3).succ P)) := by
        ring
  simpa only [hbegin, hend] using hstage

/-- The actual original source's evaluated transverse gradient has
the exact affine form b(x)+C(x)y at EVERY point.

This is derived solely from the source transverse weight bound,
not from a replacement normal-form potential or an assumed
affine-gradient equation. -/
theorem quadraticTransverseCapSource_transverseGradient_affine
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (x : K) (y : Fin 3 → K) (i : Fin 3) :
    MvPolynomial.eval (Fin.cons x y)
        (MvPolynomial.pderiv i.succ F) =
      Polynomial.eval x (quadraticTransverseCapSourceLinearCoefficients F i) +
        ∑ j : Fin 3,
          Polynomial.eval x
            ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) * y j := by
  classical
  have hsecond : ∀ j k : Fin 3,
      MvPolynomial.pderiv k.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ F)) = 0 := by
    intro j k
    exact quadraticTransverseCap_two_tripleTransversePderiv_zero
      F hcap i j k
  have hmain :=
    eval_affine_transverse_of_second_pderivs_zero
      (MvPolynomial.pderiv i.succ F) hsecond x y
  have hb :
      MvPolynomial.eval
          (Fin.cons x (fun _ : Fin 3 => (0 : K)))
          (MvPolynomial.pderiv i.succ F) =
        Polynomial.eval x (quadraticTransverseCapSourceLinearCoefficients F i) := by
    exact eval_pderiv_finCons_zero_eq_eval_longitudinalCoefficient_single
      i F x
  have hC (j : Fin 3) :
      MvPolynomial.eval
          (Fin.cons x (fun _ : Fin 3 => (0 : K)))
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F)) =
        Polynomial.eval x
          ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) := by
    rw [eval_finCons_zero_eq_longitudinalAxisRestriction]
    change Polynomial.eval x
      (longitudinalAxisRestrictionRingHom (K := K)
        (HC4.Polynomial.hessian F i.succ j.succ)) =
      Polynomial.eval x
        ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j)
    rw [quadraticTransverseCapSource_axisThreeBlock_entry]
  rw [hb] at hmain
  simp_rw [hC] at hmain
  calc
    MvPolynomial.eval (Fin.cons x y)
        (MvPolynomial.pderiv i.succ F) =
      Polynomial.eval x (quadraticTransverseCapSourceLinearCoefficients F i) +
        ∑ j : Fin 3,
          y j * Polynomial.eval x
            ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) := hmain
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

end

end HC4.Valuation
