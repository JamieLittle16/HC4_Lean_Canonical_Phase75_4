import HC4.Polynomial.RankThreeCubicDetOneFixedPoleAllPrincipalCofactors
import HC4.Polynomial.RankThreeCubicDetOneSourceGenuinePoleLowJetSquareOrTriple
import HC4.Polynomial.RankThreeCubicSourceRankOneElimination
import Mathlib.Tactic

/-!
# Elimination of the genuine cubic-pole longitudinal-only escape

At every genuine reduced denominator pole of the cubic
source characteristic, the previous source trichotomy produced:

* a nonzero quadratic TRANSVERSE repair;
* a longitudinal-only repair through the actual below-two source;
* an exact triple factor of the cubic transverse Hessian determinant.

The longitudinal-only branch is impossible.

Indeed, on that branch the full cubic source Hessian kills a
constant nonzero transverse direction w modulo the genuine
linear pole p, the quadratic transverse block also kills w,
and the quadratic mixed longitudinal coupling is divisible
by p. Determinant one then forces every cubic transverse
principal cofactor to vanish on p=0. Over the infinite
ground field this means EVERY such cofactor is divisible by p.

But the genuine source pole already carries a verified
nondivisible principal cubic cofactor, independently of the
repair split. Contradiction.

Thus only a genuine quadratic transverse repair or an exact
triple pole remains. No endpoint assumption, source shear,
auxiliary completion or algebraically closed field is used.
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

/-- The actual source's genuine cubic denominator pole requires
a NONZERO transverse quadratic correction unless the source
cubic transverse Hessian determinant is exactly a nonzero
scalar times the cube of that pole. -/
theorem sourceCubic_genuinePole_detOne_transverseRepair_or_exactTriple
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
      (∃ i : Fin 3, (C *ᵥ v) (.inr i) ≠ 0))
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L3
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  obtain ⟨ell, M, r, t, hlin, hM, hrt,
      hWne, hAker, htrace, hcase⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_lowJetSquare_or_triple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
    let W : Fin 3 → R := fun j => q (MvPolynomial.C (w0 j))
    let v : Unit ⊕ Fin 3 → R :=
      Sum.elim (fun _ : Unit => 0) W
    rcases hcase with htrans |
      ⟨hunit, hdvd, hrows, hbase, hTdet, hcoupling, hline,
        hprincipal, hflow⟩
    · exact Or.inl ⟨ell, M, r, t, hlin, hM, hrt,
        hWne, hAker, htrace, htrans⟩
    · have hw0 : w0 ≠ 0 := by
        intro hz
        apply hWne
        funext j
        simp [W, w0, hz]
      have hell : ell ≠ 0 := by
        intro hz
        have hpzero : p = 0 := by
          simpa [hz] using hlin
        exact hp.ne_zero hpzero
      have hall : ∀ k : Fin 3, p ∣ H.adjugate k k :=
        sourceCubic_fixedPoleKernel_allCubicPrincipalCofactors_dvd
          F a p ell hlin hell hcap hdetOne w0 hw0
          hAker hrows hdvd
      obtain ⟨k, hnot⟩ :=
        sourceCubic_genuinePole_has_principalRankTwo
          F a V hV hgrad hregular u p hp hpd hpn
      exact False.elim (hnot (hall k))
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
