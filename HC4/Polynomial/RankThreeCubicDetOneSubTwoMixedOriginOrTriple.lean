import HC4.Polynomial.RankThreeCubicDetOneMixedOriginSourceLayers
import Mathlib.Tactic

/-!
# The surviving mixed-origin repair comes only from the subquadratic source

Combine the genuine-pole determinant-one mixed-origin alternative
with the exact source-layer decomposition. Cubic and quadratic
source layers have positive transverse mixed-Hessian degree and
vanish at the transverse origin. Only the true strictly
subquadratic remainder R=F-L3-L2 contributes to the origin jet.

Thus every genuine source cubic pole has an explicit source-honest
trichotomy: transverse quadratic repair on the fixed kernel,
nonzero strict-subquadratic longitudinal mixed-origin repair, or
an exact scalar triple Hessian determinant factor.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] :=
  MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] :=
  FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- At the actual cubic characteristic pole, determinant one
forces either a transverse quadratic repair or a nonzero
strictly subquadratic mixed-origin source jet, unless the
pole is an exact scalar triple. -/
theorem sourceCubic_genuinePole_detOne_transverseRepair_or_subTwoMixedOrigin_or_triple
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (hregular :
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (u : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr u)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr u))) :
    let L3 := initialForm transverseCubicWeight 3 F
    let L2 := initialForm transverseCubicWeight 2 F
    let Rlow := (F - L3) - L2
    let H := sourceTransverseHessian a L3
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L3)
    let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L2)
    (∃ (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      M.det ≠ 0 ∧ (r ≠ 0 ∨ t ≠ 0) ∧
      let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
      let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun j => q (MvPolynomial.C (w0 j))
      let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        Sum.elim (fun _ : Unit => 0) W
      W ≠ 0 ∧
      A *ᵥ v = 0 ∧
      (A.adjugate * C).trace = 0 ∧
      ((∃ i : Fin 3, (C *ᵥ v) (.inr i) ≠ 0) ∨
        (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
          (∑ j : Fin 3,
            referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
              MvPolynomial.C (w0 j)) ≠ 0)))
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  obtain ⟨M, r, t, hM, hrt, hWne, hAker, htrace, hcase⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_mixedOrigin_or_triple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · refine Or.inl ⟨M, r, t, hM, hrt, hWne, hAker, htrace, ?_⟩
    rcases hcase with htrans | hmix
    · exact Or.inl htrans
    · right
      have heq :=
        sourceCubic_mixedOrigin_directional_eq_subTwo
          F a (M.mulVec ![(0 : K), r, t])
      rw [← heq]
      exact hmix
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
