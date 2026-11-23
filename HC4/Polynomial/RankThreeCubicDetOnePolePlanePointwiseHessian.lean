import HC4.Polynomial.RankThreeCubicDetOneSourceTransverseThreeScale
import Mathlib.Tactic

/-!
# Fixed transverse source kernel and constant mixed response at every pole point

An equality in K[y]/(p) can be evaluated at any K-point z with
p(z)=0. Hence a full source Hessian with transverse kernel w
and longitudinal response q(C g) modulo p has those same exact
properties over the ground field at EVERY point of the pole
plane, including 0, z, and -z.

This is the missing evaluation bridge for the three-point
determinant-one principal-cofactor obstruction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

theorem sourceHessian_fixedPoleKernel_specializes_at
    (F : SB K) (a : K) (p : B3 K)
    (w : Fin 3 → K) (g : K) :
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let B := φ.mapMatrix (hessian F)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    (∀ i : Fin 3, (B *ᵥ v) (.inr i) = 0) →
    (B *ᵥ v) (.inl ()) = q (MvPolynomial.C g) →
    ∀ z : Fin 3 → K, MvPolynomial.aeval z p = 0 →
      let ev : SB K →+* K :=
        ((MvPolynomial.aeval z).toRingHom).comp
          (referenceSlice a).toRingHom
      let Bz := ev.mapMatrix (hessian F)
      (∀ i : Fin 3,
        (∑ j : Fin 3, Bz (.inr i) (.inr j) * w j) = 0) ∧
        (∑ j : Fin 3, Bz (.inl ()) (.inr j) * w j) = g := by
  classical
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian F)
  let W : Fin 3 → R := fun j => q (MvPolynomial.C (w j))
  let v : Unit ⊕ Fin 3 → R :=
    Sum.elim (fun _ : Unit => 0) W
  change (∀ i : Fin 3, (B *ᵥ v) (.inr i) = 0) →
      (B *ᵥ v) (.inl ()) = q (MvPolynomial.C g) → _
  intro hrows hmix z hpz
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval z).toRingHom).comp
      (referenceSlice a).toRingHom
  let Bz : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    ev.mapMatrix (hessian F)
  have hresp (i : Unit ⊕ Fin 3) :
      (B *ᵥ v) i =
        q (∑ j : Fin 3,
          referenceSlice a (hessian F i (.inr j)) *
            MvPolynomial.C (w j)) := by
    simp [B, v, W, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, φ, q, map_sum, map_mul]
  constructor
  · intro i
    let f : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian F (.inr i) (.inr j)) *
          MvPolynomial.C (w j)
    have hqf : q f = 0 := by
      rw [← hresp]
      exact hrows i
    have hfz :=
      poleQuotient_zero_implies_pointEval_zero p f z hpz hqf
    simpa only [f, map_sum, map_mul, MvPolynomial.aeval_C]
      using hfz
  · let f : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian F (.inl ()) (.inr j)) *
          MvPolynomial.C (w j)
    have hqf : q f = q (MvPolynomial.C g) := by
      rw [← hresp]
      exact hmix
    have hfz :=
      poleQuotient_eq_implies_pointEval_eq
        p f (MvPolynomial.C g) z hpz hqf
    simpa only [f, map_sum, map_mul, MvPolynomial.aeval_C]
      using hfz

end
end HC4.Polynomial.RankThreeCubic
