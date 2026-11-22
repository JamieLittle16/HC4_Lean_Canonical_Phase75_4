import HC4.Polynomial.RankThreeCubicDetOneFixedTangentUnitPivot
import HC4.Polynomial.RankThreeCubicDetOneFirstCorrectionBlocks
import Mathlib.Tactic

/-!
# Source-honest genuine pole: transverse quadratic repair or a unit escape

In the nontriple genuine-pole case, the source cubic Hessian has a
nonzero fixed constant tangent kernel v=(0,W) modulo the pole.
The original Hessian has determinant one and hence is invertible.

The strict subquadratic remainder has no transverse-transverse
Hessian block. Therefore, if the quadratic Hessian does not
repair v in any of the three transverse rows, the ORIGINAL
source Hessian sends v entirely into the longitudinal axis.

Because W has a unit coordinate in the prime quotient and
the original determinant is one, the remaining longitudinal
coordinate of Hess(F)*v must be a UNIT in that quotient.

The first quadratic adjugate trace equation is retained.
The exact-triple cubic pole remains an explicit separate branch.
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

/-- A determinant-one source cannot have a genuine nontriple
cubic pole with no transverse quadratic repair unless its
full lower longitudinal response is a unit modulo that pole. -/
theorem sourceCubic_genuinePole_detOne_transverseRepair_or_unitLongitudinal_or_triple
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
    (∃ (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      M.det ≠ 0 ∧ (r ≠ 0 ∨ t ≠ 0) ∧
      let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun j => q (MvPolynomial.C
          ((M.mulVec ![(0 : K), r, t]) j))
      let v : Unit ⊕ Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        Sum.elim (fun _ : Unit => 0) W
      W ≠ 0 ∧
      A *ᵥ v = 0 ∧
      (A.adjugate * C).trace = 0 ∧
      ((∃ i : Fin 3, (C *ᵥ v) (.inr i) ≠ 0) ∨
        IsUnit ((B *ᵥ v) (.inl ()))))
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  let B : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian F)
  let C : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L2)
  let D : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian Rlow)
  obtain ⟨M, r, t, hM, hrt, hWne, hAker, htrace, _⟩ | htriple :=
    sourceCubic_genuinePole_detOne_fixedTangentRepair_or_exactTriple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · let W : Fin 3 → R :=
      fun j => q (MvPolynomial.C
        ((M.mulVec ![(0 : K), r, t]) j))
    let v : Unit ⊕ Fin 3 → R :=
      Sum.elim (fun _ : Unit => 0) W
    have hunitPivot : ∃ k : Fin 3, IsUnit (v (.inr k)) :=
      fixedTangent_has_unitPivot_in_irreducibleQuotient
        p hp M hM r t hrt
    have hdetB : B.det = 1 := by
      calc
        B.det = φ (hessian F).det := by
          exact (RingHom.map_det φ (hessian F)).symm
        _ = 1 := by
          change φ (hessianDeterminant F) = 1
          rw [hdetOne]
          simp
    have hBdecomp : B = A + (C + D) := by
      apply Matrix.ext
      intro i j
      change φ (hessian F i j) =
        φ (hessian L3 i j) +
          (φ (hessian L2 i j) + φ (hessian Rlow i j))
      have hh : hessian F i j =
          hessian L3 i j + hessian L2 i j +
            hessian Rlow i j := by
        have hx := sourceCubic_hessian_three_two_lower_decomposition F
        exact congrFun (congrFun hx i) j
      rw [hh, map_add, map_add]
      ring
    have hDtrans (i j : Fin 3) :
        D (.inr i) (.inr j) = 0 := by
      change φ (hessian Rlow (.inr i) (.inr j)) = 0
      have hz :=
        sourceCubic_belowTwo_transverseHessian_zero F hcap i j
      rw [sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F] at hz
      rw [hz]
      simp
    have hDrow (i : Fin 3) :
        (D *ᵥ v) (.inr i) = 0 := by
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        v, hDtrans]
    have hresult :
        (∃ i : Fin 3, (C *ᵥ v) (.inr i) ≠ 0) ∨
          IsUnit ((B *ᵥ v) (.inl ())) := by
      by_cases hC : ∃ i : Fin 3, (C *ᵥ v) (.inr i) ≠ 0
      · exact Or.inl hC
      · right
        have hCrows (i : Fin 3) : (C *ᵥ v) (.inr i) = 0 := by
          by_contra hn
          exact hC ⟨i, hn⟩
        have hBrows (i : Fin 3) : (B *ᵥ v) (.inr i) = 0 := by
          rw [hBdecomp, Matrix.add_mulVec, Matrix.add_mulVec]
          have hArow : (A *ᵥ v) (.inr i) = 0 := by
            have hx := congrFun hAker (.inr i)
            simpa only [Pi.zero_apply] using hx
          simp only [Pi.add_apply, hArow, hCrows i, hDrow i,
            zero_add, add_zero]
        obtain ⟨k, hk⟩ := hunitPivot
        exact detOne_pureLongitudinal_output_isUnit
          B v k hdetB hk hBrows
    exact Or.inl ⟨M, r, t, hM, hrt, hWne, hAker, htrace, hresult⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
