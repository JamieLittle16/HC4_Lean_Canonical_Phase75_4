import HC4.Polynomial.RankThreeCubicDetOneSourceSchurLowJetSquare
import HC4.Polynomial.RankThreeCubicPrincipalKernelPivot
import HC4.Polynomial.RankThreeCubicDetOneSourceQuadraticPrincipalCofactor
import HC4.Polynomial.RankThreeCubicDetOneSourceOriginSubTwoCoupling
import HC4.Polynomial.RankThreeCubicSourceNormalAdjugateOrTriple
import Mathlib.Tactic

/-!
# Exact scalar-square constraint on the surviving cubic source pole

The earlier source genuine-pole trichotomy supplied an exact
source-origin rank-two quadratic block, a principal Schur pivot,
and a strictly below-two mixed source coefficient g != 0.

The determinant-one identity in the ORIGINAL principal chart gives
    adj(T)[k,k] * g^2 = -w0[k]^2.

Thus the source Hessian's principal cofactor and its lower-layer
mixed scalar are constrained by the original kernel coordinate.

This theorem retains both other genuine-pole alternatives
(transverse quadratic repair and exact triple pole) unchanged.
There is no assumed endpoint and no contradiction claimed.
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
theorem sourceCubic_genuinePole_detOne_transverseRepair_or_lowJetSquare_or_triple
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
      let T : Matrix (Fin 3) (Fin 3) K :=
        fun i j => MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
          (referenceSlice a (hessian L2 (.inr i) (.inr j)))
      let ev : SB K →+* K :=
        ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
          (referenceSlice a).toRingHom
      let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
        ev.mapMatrix (hessian F)
      let Rlow : SB K := (F - L3) - L2
      let flow : B3 K :=
        ∑ j : Fin 3,
          referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
            MvPolynomial.C (w0 j)
      W ≠ 0 ∧
      A *ᵥ v = 0 ∧
      (A.adjugate * C).trace = 0 ∧
      ((∃ i : Fin 3, (C *ᵥ v) (.inr i) ≠ 0) ∨
        (IsUnit ((B *ᵥ v) (.inl ())) ∧
          p ∣ (∑ j : Fin 3,
            referenceSlice a (hessian L2 (.inl ()) (.inr j)) *
              MvPolynomial.C (w0 j)) ∧
          (∀ i : Fin 3, (C *ᵥ v) (.inr i) = 0) ∧
          (∀ i : Fin 3, ∑ j : Fin 3,
            (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
              (referenceSlice a (hessian L2 (.inr i) (.inr j)))) *
                w0 j = 0) ∧
          T.det = 0 ∧
          (∑ j : Fin 3, B0 (.inl ()) (.inr j) * w0 j) ≠ 0 ∧
          (∀ z : Fin 3 → K, T *ᵥ z = 0 →
            ∃ c : K, ∀ j : Fin 3, z j = c * w0 j) ∧
          (∃ k : Fin 3,
            let H0 := principalSourceFourBlock B0 k
            T.adjugate k k ≠ 0 ∧ w0 k ≠ 0 ∧
            H0.activeDet = T.adjugate k k ∧
            H0.schurC = 0 ∧
            H0.determinantCore = 1 ∧
            H0.schurB ^ 2 = -T.adjugate k k ∧
            H0.schurB ≠ 0 ∧
            H0.activeDet * flow.coeff 0 = H0.schurB * w0 k ∧
            T.adjugate k k * (flow.coeff 0) ^ 2 = -(w0 k ^ 2)) ∧
          flow.coeff 0 ≠ 0)))
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
  obtain ⟨ell, M, r, t, hlin, hM, hrt,
      hWne, hAker, htrace, hcase⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_sourceSchurSquare_or_triple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
    let W : Fin 3 → R := fun j => q (MvPolynomial.C (w0 j))
    let v : Unit ⊕ Fin 3 → R :=
      Sum.elim (fun _ : Unit => 0) W
    let T : Matrix (Fin 3) (Fin 3) K :=
      fun i j => MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))
        (referenceSlice a (hessian L2 (.inr i) (.inr j)))
    let ev : SB K →+* K :=
      ((MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))).toRingHom).comp
        (referenceSlice a).toRingHom
    let B0 : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) K :=
      ev.mapMatrix (hessian F)
    let Rlow : SB K := (F - L3) - L2
    let flow : B3 K :=
      ∑ j : Fin 3,
        referenceSlice a (hessian Rlow (.inl ()) (.inr j)) *
          MvPolynomial.C (w0 j)
    refine Or.inl ⟨ell, M, r, t, hlin, hM, hrt,
      hWne, hAker, htrace, ?_⟩
    rcases hcase with htrans | ⟨hunit, hdvd, hrows,
        hbase, hTdet, hcoupling, hline,
        ⟨k, hk, hwk, hactive, hC, hdetH, hsq, hsnz⟩, hflow⟩
    · exact Or.inl htrans
    · have hw0 : w0 ≠ 0 := by
        intro hz
        apply hwk
        simpa only [Pi.zero_apply] using congrFun hz k
      obtain ⟨hpair, hlowSquare⟩ :=
        sourceCubic_detOne_originSchur_lowJetSquare
          F a hcap hdetOne w0 hw0 hbase k hk
      have hlowSquare' :
          T.adjugate k k * (flow.coeff 0) ^ 2 =
            -(w0 k ^ 2) := by
        rw [← hactive]
        exact hlowSquare
      exact Or.inr ⟨hunit, hdvd, hrows, hbase, hTdet,
        hcoupling, hline, ⟨k, hk, hwk, hactive, hC,
          hdetH, hsq, hsnz, hpair, hlowSquare'⟩, hflow⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
