import HC4.Valuation.QuadraticTransverseCapSourceHessianFlat
import Mathlib.Tactic

/-!
# Exact affine evaluations on source transverse basis sections

If a multivariate polynomial P has zero second formal derivative
in the source coordinate i, then evaluation at two points which
differ only in i is exactly affine in the coordinate difference.

We prove this by differentiating P - X_i * ∂_i P, which is
independent of i, and applying the existing source evaluation
independence theorem. This does not assume an analytic Taylor
expansion or an invented polynomial source.

The specialisation to the honest source sections y=t e_j gives
a K[x]-polynomial identity, ready for the mixed-Hessian adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Exact affine evaluation in one coordinate whenever its
second partial derivative vanishes. The remaining coordinates
may be arbitrary; the base point has i-coordinate zero. -/
theorem mvPolynomial_eval_affine_of_secondPderiv_zero
    (P : MvPolynomial (Fin 4) K)
    (i : Fin 4)
    (hsecond :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i P) = 0)
    (p q : Fin 4 → K)
    (hpi : p i = 0)
    (heq : ∀ j : Fin 4, j ≠ i → p j = q j) :
    MvPolynomial.eval q P =
      MvPolynomial.eval p P +
        q i * MvPolynomial.eval p (MvPolynomial.pderiv i P) := by
  let D := MvPolynomial.pderiv i P
  let R := P - MvPolynomial.X i * D
  have hR : MvPolynomial.pderiv i R = 0 := by
    simp [R, D, MvPolynomial.pderiv_mul, hsecond]
  have hRval : MvPolynomial.eval p P =
      MvPolynomial.eval q P -
        q i * MvPolynomial.eval q D := by
    have h := HC4.Newton.eval_eq_of_pderiv_eq_zero
      i R hR p q heq
    simpa [R, hpi] using h
  have hDval :
      MvPolynomial.eval p D = MvPolynomial.eval q D :=
    HC4.Newton.eval_eq_of_pderiv_eq_zero
      i D hsecond p q heq
  calc
    MvPolynomial.eval q P =
        MvPolynomial.eval p P +
          q i * MvPolynomial.eval q D := by
            linear_combination -hRval
    _ = MvPolynomial.eval p P +
          q i * MvPolynomial.eval p D := by
            rw [← hDval]

/-- For any source with vanishing second derivative in the
transverse coordinate j, its restriction to the section
y=t e_j differs from the marked-axis restriction by exactly
t times the restricted first transverse derivative.

This is a POLYNOMIAL identity in x₀, not an evaluated equality at
a selected longitudinal parameter. -/
theorem quadraticTransverseSource_affineBasisSection
    (P : MvPolynomial (Fin 4) K)
    (j : Fin 3)
    (hsecond :
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv j.succ P) = 0)
    (t : K) :
    quadraticTransverseSourceSectionRingHom
        (fun k : Fin 3 => if k = j then t else 0) P =
      longitudinalAxisRestrictionRingHom (K := K) P +
        Polynomial.C t *
          longitudinalAxisRestrictionRingHom (K := K)
            (MvPolynomial.pderiv j.succ P) := by
  apply Polynomial.funext
  intro x
  let y : Fin 3 → K := fun k => if k = j then t else 0
  let p : Fin 4 → K :=
    Fin.cons x (fun _ : Fin 3 => (0 : K))
  let q : Fin 4 → K := Fin.cons x y
  have hp : p j.succ = 0 := by
    simp [p]
  have heq : ∀ k : Fin 4, k ≠ j.succ → p k = q k := by
    intro k hk
    refine Fin.cases ?_ (fun a => ?_) k
    · rfl
    · have haj : a ≠ j := by
        intro he
        apply hk
        simp [he]
      simp [p, q, y, haj]
  have hval :=
    mvPolynomial_eval_affine_of_secondPderiv_zero
      P j.succ hsecond p q hp heq
  have hq : q j.succ = t := by
    simp [q, y]
  have hpoly (Q : MvPolynomial (Fin 4) K) :
      Polynomial.eval x (longitudinalAxisRestrictionRingHom (K := K) Q) =
        MvPolynomial.eval p Q := by
    rw [← quadraticTransverseSourceSectionRingHom_zero]
    simpa [p] using
      (quadraticTransverseSourceSectionRingHom_eval
        Q x (fun _ : Fin 3 => (0 : K)))
  calc
    Polynomial.eval x
        (quadraticTransverseSourceSectionRingHom
          (fun k : Fin 3 => if k = j then t else 0) P) =
        MvPolynomial.eval q P := by
          exact quadraticTransverseSourceSectionRingHom_eval P x y
    _ = MvPolynomial.eval p P +
          t * MvPolynomial.eval p
            (MvPolynomial.pderiv j.succ P) := by
          simpa only [hq] using hval
    _ = Polynomial.eval x
          (longitudinalAxisRestrictionRingHom (K := K) P +
            Polynomial.C t *
              longitudinalAxisRestrictionRingHom (K := K)
                (MvPolynomial.pderiv j.succ P)) := by
          simp [hpoly]

end

end HC4.Valuation
