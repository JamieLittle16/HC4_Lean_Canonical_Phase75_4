import HC4.Polynomial.RankThreeCubicDetOneFixedTangentQuadraticDivisibilityOrTriple
import Mathlib.Tactic

/-!
# Descent of a pole-quotient transverse kernel to the original ground field

If the linear pole hyperplane p=0 passes through the transverse
origin, evaluation at y=0 kills the ideal (p). Thus any quotient
equation q(f)=0 gives f(0)=0 over the original field K.

Applied to the source's weight-two transverse Hessian and a fixed
constant transverse direction W, this converts the no-transverse-
repair condition from K[y]/(p) into an exact source Hessian kernel
at the original longitudinal anchor and transverse origin.

This is more precise than saying the quotient matrix is singular:
the vector and the resulting kernel equation live in K itself.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- If a polynomial is zero modulo an ideal (p) whose generator
vanishes at the origin, it vanishes at the origin already in K. -/
theorem poleQuotient_zero_implies_originEval_zero
    (p f : B3 K)
    (hp0 : MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) p = 0)
    (hf : Ideal.Quotient.mk (Ideal.span {p}) f = 0) :
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K)) f = 0 := by
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hf
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
  rw [hg, map_mul, hp0, zero_mul]

/-- In the source's actual quadratic layer, a constant transverse
direction killed by the transverse Hessian modulo p is killed by
that Hessian at the origin over the ground field K itself. -/
theorem sourceCubic_quadraticTransverseKernel_descends_to_origin
    (F : SB K) (a : K)
    (p : B3 K) (ell : Fin 3 → K)
    (hlin : p = ∑ i : Fin 3,
      (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i))
    (w0 : Fin 3 → K) :
    let L2 := initialForm transverseCubicWeight 2 F
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L2)
    let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      fun j => q (MvPolynomial.C (w0 j))
    let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
      Sum.elim (fun _ : Unit => 0) W
    (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) →
      ∀ i : Fin 3,
        ∑ j : Fin 3,
          (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
            (referenceSlice a (hessian L2 (.inr i) (.inr j)))) *
            w0 j = 0 := by
  classical
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
    q.comp (referenceSlice a).toRingHom
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
      (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L2)
  let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    fun j => q (MvPolynomial.C (w0 j))
  let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
    Sum.elim (fun _ : Unit => 0) W
  change (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) → _
  intro hrows i
  let frow : B3 K :=
    ∑ j : Fin 3,
      referenceSlice a (hessian L2 (.inr i) (.inr j)) *
        MvPolynomial.C (w0 j)
  have hqrow : q frow = 0 := by
    have hi := hrows i
    simpa [frow, C, v, W, φ, q, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type,
      map_sum, map_mul] using hi
  have hfzero :=
    poleQuotient_zero_implies_originEval_zero p frow
      (linearPole_originEval_eq_zero p ell hlin) hqrow
  simpa [frow, map_sum, map_mul] using hfzero

end
end HC4.Polynomial.RankThreeCubic
