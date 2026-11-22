import HC4.Polynomial.RankThreeCubicDetOneUnitSourceMixedOrigin
import HC4.Polynomial.RankThreeCubicSourceNormalAdjugateOrTriple
import Mathlib.Tactic

/-!
# Genuine cubic pole: transverse repair or nonzero source mixed-origin jet

The unit-valued longitudinal repair established from the original
determinant-one Hessian is tested at the transverse origin of the
actual pole hyperplane. A homogeneous linear denominator prime
passes through this origin.

In the nontriple branch this yields a concrete source condition:
either the true quadratic layer repairs a transverse Hessian row
of the fixed tangent vector, or the ORIGINAL source mixed Hessian
has a nonzero directional pairing at (x=a,y=0).

This is strictly stronger than asking that the pairing be nonzero
in the pole quotient: the latter alone can be nonzero with
vanishing constant term. No endpoint hypothesis is inserted;
the exact-triple alternative remains explicit.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

/-- A genuine source cubic denominator pole has either a
nonzero transverse quadratic repair, a nonzero original-source
mixed Hessian pairing at the transverse origin, or an exact
nonzero scalar triple factor. The same fixed tangent direction
and quotient remain in the nontriple branch. -/
theorem sourceCubic_genuinePole_detOne_transverseRepair_or_mixedOrigin_or_triple
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
            referenceSlice a (hessian F (.inl ()) (.inr j)) *
              MvPolynomial.C (w0 j)) ≠ 0)))
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian F)
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  obtain ⟨c, ell, k, hfactor, hc, hlin, hcof, hnormal⟩ :=
    sourceCubic_genuineRankTwo_adjugateNormalZero_or_triple
      F a V hV hgrad hregular u p hp hpd hpn
  obtain ⟨M, r, t, hM, hrt, hWne, hAker, htrace, hrepair⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_unitLongitudinal_or_triple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
    let W : Fin 3 → R := fun j => q (MvPolynomial.C (w0 j))
    let v : Unit ⊕ Fin 3 → R :=
      Sum.elim (fun _ : Unit => 0) W
    refine Or.inl ⟨M, r, t, hM, hrt, hWne, hAker, htrace, ?_⟩
    rcases hrepair with htrans | hunit
    · exact Or.inl htrans
    · right
      exact unitLongitudinal_sourceMixedOrigin_ne_zero
        F a p ell hlin w0 hunit
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
