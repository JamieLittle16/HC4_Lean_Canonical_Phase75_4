import HC4.Polynomial.RankThreeCubicDetOneUnitSourceQuadraticMixedDivisibility
import HC4.Polynomial.RankThreeCubicSourceNormalAdjugateOrTriple
import Mathlib.Tactic

/-!
# Determinant-one genuine cubic pole: transverse quadratic repair
# or quadratic longitudinal repair divisible by the actual pole

For an actual denominator prime of the cubic source characteristic,
the source provides its homogeneous linear pole equation p=ell·y.
In the nontriple branch it also provides an invertible transverse
frame M and a constant nonzero tangent direction w0=M(0,r,t).

The fixed cubic Hessian kills (0,w0) modulo p. If the quadratic
source Hessian does not repair a transverse row, determinant one
forces the full longitudinal response to be a unit modulo p.

The source-affine-unit theorem now implies that the ORIGINAL
quadratic mixed Hessian pairing
  sum_j referenceSlice_a Hess(L2)_(x,j) * C(w0_j)
is divisible by the genuine denominator prime p.

All of the data is inherited from the genuine source pole, and
the exact scalar triple factor remains a separate alternative.
This is still a necessary condition, not a contradiction.
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

/-- Every genuine source cubic denominator pole is either an
exact scalar triple or has a nonzero fixed tangent kernel
that forces a transverse quadratic repair OR a unit
longitudinal repair whose linear quadratic-source part is
divisible by the actual homogeneous linear prime p. -/
theorem sourceCubic_genuinePole_detOne_transverseRepair_or_quadraticMixedDvd_or_triple
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
    let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian F)
    let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L2)
    (∃ (ell : Fin 3 → K)
        (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
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
        (IsUnit ((B *ᵥ v) (.inl ())) ∧
          p ∣ (∑ j : Fin 3,
            referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
              MvPolynomial.C (w0 j)))))
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
  have hell : ell ≠ 0 := by
    intro he
    apply hp.ne_zero
    rw [hlin, he]
    simp
  obtain ⟨M, r, t, hM, hrt, hWne, hAker, htrace, hcase⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_unitLongitudinal_or_triple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · refine Or.inl ⟨ell, M, r, t, hlin, hM, hrt, hWne, hAker, htrace, ?_⟩
    rcases hcase with htrans | hunit
    · exact Or.inl htrans
    · right
      refine ⟨hunit, ?_⟩
      exact sourceCubic_unitLongitudinal_implies_secondLayer_mixed_dvd
        F hcap a p ell hlin hell (M.mulVec ![(0 : K), r, t])
        hAker hunit
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
