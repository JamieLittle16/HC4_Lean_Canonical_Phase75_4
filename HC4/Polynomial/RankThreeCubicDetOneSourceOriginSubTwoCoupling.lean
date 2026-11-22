import HC4.Polynomial.RankThreeCubicDetOneSourceGenuinePoleKernelLineOrTriple
import Mathlib.Tactic

/-!
# Source-honest origin coupling from the strictly subquadratic layer

The weight-three and weight-two source layers contribute zero to
the mixed longitudinal/transverse Hessian at the transverse origin.

Hence the longitudinal pairing at (a,0) of the *actual* Hessian
of F with any constant transverse direction w is exactly the
mixed-origin pairing of its strict-below-two remainder.

A determinant-one full source Hessian with a nonzero quadratic
transverse kernel therefore forces this actual lower-layer
mixed-origin coefficient to be nonzero.

These are exact source coefficients, not free choices of repair data.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- At the true transverse origin, the entire directional
longitudinal mixed Hessian response comes from the strict
subquadratic source remainder. -/
theorem sourceCubic_originLongitudinalPairing_eq_subTwo
    (F : SB K) (a : K) (w0 : Fin 3 → K) :
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    (∑ j : Fin 3,
      ev (hessian F (.inl ()) (.inr j)) * w0 j) =
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)) := by
  classical
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2 F
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  have h := sourceCubic_mixedOrigin_directional_eq_subTwo F a w0
  simpa [ev, Rlow, map_sum, map_mul] using h

/-- Under det(Hess(F))=1, any nonzero kernel vector of the
true quadratic transverse Hessian at (a,0) has a nonzero
strict-subquadratic longitudinal mixed-origin response. -/
theorem sourceCubic_detOne_originQuadraticKernel_subTwoCoupling_ne_zero
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
    let Rlow : SB K :=
      (F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F
    MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
      (∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)) ≠ 0 := by
  classical
  let Rlow : SB K :=
    (F - initialForm transverseCubicWeight 3 F) -
      initialForm transverseCubicWeight 2 F
  let ev : SB K →+* K :=
    ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
      (referenceSlice a).toRingHom
  let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
    ev.mapMatrix (hessian F)
  obtain ⟨hcoupling, _⟩ :=
    sourceCubic_detOne_originQuadraticKernel_isLine
      F a hcap hdetOne w0 hw0 hTker
  have hc : (∑ j : Fin 3,
      ev (hessian F (.inl ()) (.inr j)) * w0 j) ≠ 0 := by
    exact hcoupling
  have heq := sourceCubic_originLongitudinalPairing_eq_subTwo F a w0
  rw [heq] at hc
  exact hc

end
end HC4.Polynomial.RankThreeCubic
