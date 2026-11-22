import HC4.Polynomial.RankThreeCubicDetOnePoleRepairDichotomyAlgebra
import HC4.Polynomial.RankThreeCubicDetOneFirstCorrectionBlocks
import Mathlib.Tactic

/-!
# Genuine cubic pole: quadratic vector repair or lower longitudinal escape

The source polynomial F is split into its *actual* transverse weight
3 and 2 components plus R=F-L3-L2, with weight(R)<2.
Its R Hessian has identically zero transverse-transverse block.

Combine this structure with the genuine denominator-pole residue
already constructed by the source transport theorem, the
nonvanishing determinant-one repair, and the independent weight-five
adjugate-trace equation. A source-honest necessary alternative:

* quadratic source Hessian acts nontrivially on the residue; OR
* the strict-subquadratic remainder repairs through its
  longitudinal/transverse Hessian row.

The alternative is not claimed to be contradictory. It isolates
the only remaining avenue for a repair invisible to the quadratic
source Hessian.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators
noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- For the actual denominator pole, the first quadratic source
correction must either act nontrivially on the normalized residue
or the strict subquadratic source remainder must have a nonzero
longitudinal mixed-row pairing with that residue.

The weight-five adjugate-trace zero constraint holds simultaneously
for the same source, anchor, quotient and pole residue. -/
theorem sourceCubic_genuinePole_detOne_quadratic_or_lowerMixed_repair
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
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L3)
    ∃ (k : Fin 3) (S : Fin 3 → (B3 K ⧸ Ideal.span {p})),
      S k ≠ 0 ∧
      A *ᵥ (Sum.elim (fun _ : Unit =>
        (0 : B3 K ⧸ Ideal.span {p})) S) = 0 ∧
      (A.adjugate * φ.mapMatrix (hessian L2)).trace = 0 ∧
      ((φ.mapMatrix (hessian L2)) *ᵥ
         (Sum.elim (fun _ : Unit =>
           (0 : B3 K ⧸ Ideal.span {p})) S) ≠ 0 ∨
       (∑ j : Fin 3,
          (φ.mapMatrix (hessian Rlow)) (.inl ()) (.inr j) *
            S j) ≠ 0) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let Rlow : SB K := (F - L3) - L2
  let E : SB K := F - L3
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R := q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  obtain ⟨k, S, hSk, hAw, htrace, hrepair⟩ :=
    sourceCubic_genuinePole_detOne_firstCorrection_compatibility
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  have hER : E = L2 + Rlow := by
    dsimp [E, Rlow]
    ring
  have hmatrix :
      φ.mapMatrix (hessian E) =
        φ.mapMatrix (hessian L2) +
          φ.mapMatrix (hessian Rlow) := by
    apply Matrix.ext
    intro i j
    change φ (hessian E i j) =
      φ (hessian L2 i j) + φ (hessian Rlow i j)
    rw [hER]
    simp only [hessian_apply, map_add]
  have hRtrans (i j : Fin 3) :
      hessian Rlow (.inr i) (.inr j) = 0 := by
    change hessian
      ((F - initialForm transverseCubicWeight 3 F) -
        initialForm transverseCubicWeight 2 F)
      (.inr i) (.inr j) = 0
    rw [← sourceCubic_remainder_secondLayer_eq_sourceSecondLayer F]
    exact sourceCubic_belowTwo_transverseHessian_zero F hcap i j
  have hDtrans (i j : Fin 3) :
      (φ.mapMatrix (hessian Rlow)) (.inr i) (.inr j) = 0 := by
    change φ (hessian Rlow (.inr i) (.inr j)) = 0
    rw [hRtrans]
    simp
  have hnewRepair :
      (φ.mapMatrix (hessian L2) +
        φ.mapMatrix (hessian Rlow)) *ᵥ
          (Sum.elim (fun _ : Unit => (0 : R)) S) ≠ 0 := by
    rw [← hmatrix]
    exact hrepair
  have hsplit :=
    zeroLongitudinalVector_repair_secondLayer_or_lowerMixed
      (φ.mapMatrix (hessian L2))
      (φ.mapMatrix (hessian Rlow))
      S hDtrans hnewRepair
  exact ⟨k, S, hSk, hAw, htrace, hsplit⟩

end
end HC4.Polynomial.RankThreeCubic
