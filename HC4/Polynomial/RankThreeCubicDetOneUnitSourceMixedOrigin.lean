import HC4.Polynomial.RankThreeCubicDetOnePoleUnitOrigin
import Mathlib.Tactic

/-!
# Unit longitudinal response forces a nonzero source mixed-origin pairing

For an actual source polynomial F, its longitudinal Hessian response
to a fixed transverse vector w0 is the reduction modulo p of the
polynomial
   f = sum_j (referenceSlice_a (Hess F)_(x,j)) * C(w0_j).

If p is a homogeneous linear hyperplane equation through the origin
and the response is a unit modulo p, then f(0) is nonzero. This is
an exact original-source condition, not a matrix-only constraint.

The theorem is intentionally separated from the genuine-pole case
split, so the quotient/evaluation identity can be checked on its own.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- A unit longitudinal response on a source-derived constant
transverse direction forces the ORIGINAL source mixed Hessian
to have nonzero directional pairing at the transverse origin. -/
theorem unitLongitudinal_sourceMixedOrigin_ne_zero
    (F : SB K) (a : K)
    (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (w0 : Fin 3 → K) :
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian F)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w0 j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    IsUnit ((B *ᵥ v) (.inl ())) →
      MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
        (∑ j : Fin 3,
          referenceSlice a (hessian F (.inl ()) (.inr j)) *
            MvPolynomial.C (w0 j)) ≠ 0 := by
  classical
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
    q.comp (referenceSlice a).toRingHom
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
      (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian F)
  let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun j => q (MvPolynomial.C (w0 j))
  let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    Sum.elim (fun _ : Unit => 0) W
  let f : B3 K := ∑ j : Fin 3,
    referenceSlice a (hessian F (.inl ()) (.inr j)) *
      MvPolynomial.C (w0 j)
  have hresp : (B *ᵥ v) (.inl ()) = q f := by
    simp [B, v, W, f, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, φ, q, map_sum, map_mul]
  change IsUnit ((B *ᵥ v) (.inl ())) →
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) f ≠ 0
  intro hunit
  have hu : IsUnit (q f) := by
    rw [← hresp]
    exact hunit
  exact linearPoleQuotient_unit_implies_originEval_ne_zero
    p ell hlin f hu

end
end HC4.Polynomial.RankThreeCubic
