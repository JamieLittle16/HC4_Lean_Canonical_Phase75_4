import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleSlice
import Mathlib.Tactic

/-!
# The genuine cubic pole's first-order repair compatibility

Combine two independently established source facts over ONE prime
quotient at ONE longitudinal anchor:

(1) the nonzero normalized cubic denominator residue lies in the
    kernel of the cubic Hessian but is NOT killed by the lower source
    Hessian repair;
(2) the exact quadratic source layer has zero adjugate-trace pairing
    with that same cubic Hessian, as forced by det Hess F = 1.

No auxiliary endpoint assumptions are inserted; the assumptions
are precisely the actual source cubic cap, determinant one,
gradient transport and denominator pole hypotheses.

This is a compatibility statement, NOT proof that the two demands
are contradictory. In particular, vanishing of a scalar trace
pairing does not directly imply annihilation of a kernel vector.
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

/-- Every genuine cubic pole residue must simultaneously satisfy
the exact quadratic adjugate-trace equation and be repaired
nontrivially by the full original lower Hessian layers. -/
theorem sourceCubic_genuinePole_detOne_firstCorrection_compatibility
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
    let E := F - L3
    let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
      Ideal.Quotient.mk (Ideal.span {p})
    let φ : SB K →+* (B3 K ⧸ Ideal.span {p}) :=
      q.comp (referenceSlice a).toRingHom
    let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3)
        (B3 K ⧸ Ideal.span {p}) := φ.mapMatrix (hessian L3)
    ∃ (k : Fin 3) (S : Fin 3 → (B3 K ⧸ Ideal.span {p})),
      S k ≠ 0 ∧
      A *ᵥ (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) = 0 ∧
      (A.adjugate * φ.mapMatrix (hessian L2)).trace = 0 ∧
      (φ.mapMatrix (hessian E)) *ᵥ
        (Sum.elim (fun _ : Unit => (0 : B3 K ⧸ Ideal.span {p})) S) ≠ 0 := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let L2 : SB K := initialForm transverseCubicWeight 2 F
  let E : SB K := F - L3
  let R := B3 K ⧸ Ideal.span {p}
  let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
  let φ : SB K →+* R :=
    q.comp (referenceSlice a).toRingHom
  let A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R :=
    φ.mapMatrix (hessian L3)
  obtain ⟨k, S, hSk, _hprofile, hAw, hRepair⟩ :=
    sourceCubic_genuinePole_detOne_strictLowerWeightRepair
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  have htrace :
      (A.adjugate * φ.mapMatrix (hessian L2)).trace = 0 :=
    sourceCubic_detOne_slicedPole_firstCorrection_trace_zero
      F hcap hdetOne a p
  exact ⟨k, S, hSk, hAw, htrace, hRepair⟩

end
end HC4.Polynomial.RankThreeCubic
