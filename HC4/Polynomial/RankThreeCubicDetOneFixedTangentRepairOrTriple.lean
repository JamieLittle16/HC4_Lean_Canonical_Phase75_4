import HC4.Polynomial.RankThreeCubicDetOneFixedTangentNonzero
import HC4.Polynomial.RankThreeCubicDetOnePoleRepairDichotomyAlgebra
import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleSlice
import HC4.Polynomial.RankThreeCubicDetOneFirstCorrectionBlocks
import Mathlib.Tactic

/-!
# Genuine cubic source pole: fixed-direction repair or exact triple pole

The nontriple branch has a source-derived constant tangent vector
W=M*(0,r,t), annihilated by the full cubic Hessian modulo the
actual denominator prime. This W is nonzero in the prime quotient.

Determinant one forces the complete lower Hessian to repair W.
After separating the true quadratic layer from the strictly
subquadratic remainder, the latter contributes no transverse
Hessian rows, so either the quadratic Hessian acts nontrivially
on W or its remaining longitudinal mixed row pairs nontrivially
with W.

The source-derived weight-five adjugate trace equation holds
simultaneously. The exact-triple branch remains an explicit
alternative. No invented residue witness or rank hypothesis.
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

/-- A genuine source cubic denominator pole has either an exact
nonzero scalar triple factor, or a nonzero *fixed* tangent kernel
on its plane which determinant one must repair by the exact
quadratic Hessian or the strictly lower longitudinal mixed row.

The first weight-five adjugate trace constraint is retained in
the very same slice and prime quotient. -/
theorem sourceCubic_genuinePole_detOne_fixedTangentRepair_or_exactTriple
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
    (∃ (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      M.det ≠ 0 ∧ (r ≠ 0 ∨ t ≠ 0) ∧
      let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun j => q (MvPolynomial.C
          ((M.mulVec ![(0 : K), r, t]) j))
      let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        Sum.elim (fun _ : Unit => 0) W
      W ≠ 0 ∧
      A *ᵥ v = 0 ∧
      (A.adjugate * φ.mapMatrix (hessian L2)).trace = 0 ∧
      ((φ.mapMatrix (hessian L2)) *ᵥ v ≠ 0 ∨
        (∑ j : Fin 3,
          (φ.mapMatrix (hessian Rlow)) (.inl ()) (.inr j) *
            W j) ≠ 0))
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R :=
    q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian F)
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  let D : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian Rlow)
  obtain ⟨M, r, t, hM, hrt, hAw⟩ | htriple :=
    sourceCubic_genuinePole_fourHessianFixedTangent_or_exactTriple
      F a V hV hgrad hregular u p hp hpd hpn
  · let W : Fin 3 → R :=
      fun j => q (MvPolynomial.C
        ((M.mulVec ![(0 : K), r, t]) j))
    let v : Unit ⊕ Fin 3 → R :=
      Sum.elim (fun _ : Unit => 0) W
    have hWne : W ≠ 0 :=
      fixedTangent_nonzero_in_irreducibleQuotient
        p hp M hM r t hrt
    have hvne : v ≠ 0 := by
      intro hv
      apply hWne
      funext j
      have hi := congrFun hv (.inr j)
      simpa only [v, Pi.zero_apply] using hi
    have hAker : A *ᵥ v = 0 := by
      exact hAw
    have hdetB : B.det = 1 := by
      calc
        B.det = φ (hessian F).det := by
          exact (RingHom.map_det φ (hessian F)).symm
        _ = 1 := by
          change φ (hessianDeterminant F) = 1
          rw [hdetOne]
          simp
    have hmatrix : A + (C + D) = B := by
      apply Matrix.ext
      intro i j
      change φ (hessian L3 i j) +
          (φ (hessian L2 i j) + φ (hessian Rlow i j)) =
        φ (hessian F i j)
      have hh : hessian F i j =
          hessian L3 i j + hessian L2 i j +
            hessian Rlow i j := by
        have hx := sourceCubic_hessian_three_two_lower_decomposition F
        exact congrFun (congrFun hx i) j
      rw [hh, map_add, map_add]
      ring
    have hdetSum : (A + (C + D)).det = 1 := by
      rw [hmatrix]
      exact hdetB
    have hrepair : (C + D) *ᵥ v ≠ 0 :=
      detOne_matrix_correction_nonzero_on_kernel
        A (C + D) v hdetSum hAker hvne
    have hRtrans (i j : Fin 3) :
        hessian Rlow (.inr i) (.inr j) = 0 := by
      have hz :=
        sourceCubic_belowTwo_transverseHessian_zero F hcap i j
      rw [sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F] at hz
      exact hz
    have hDtrans (i j : Fin 3) :
        D (.inr i) (.inr j) = 0 := by
      change φ (hessian Rlow (.inr i) (.inr j)) = 0
      rw [hRtrans]
      simp
    have htrace : (A.adjugate * C).trace = 0 :=
      sourceCubic_detOne_slicedPole_firstCorrection_trace_zero
        F hcap hdetOne a p
    have hsplit :
        C *ᵥ v ≠ 0 ∨
          (∑ j : Fin 3, D (.inl ()) (.inr j) * W j) ≠ 0 :=
      zeroLongitudinalVector_repair_secondLayer_or_lowerMixed
        C D W hDtrans hrepair
    exact Or.inl ⟨M, r, t, hM, hrt, hWne, hAker, htrace, hsplit⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
