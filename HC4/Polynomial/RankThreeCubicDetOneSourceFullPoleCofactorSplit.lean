import HC4.Polynomial.RankThreeCubicDetOneSourceRankThreeRepairIsotropicFromPivot
import HC4.Polynomial.RankThreeCubicDetOneSourceTransverseRepairOriginWitness
import Mathlib.Tactic

/-!
# Source-honest full-cubic-Hessian cofactor split at a genuine pole

A genuine cubic characteristic pole under the original determinant-one
source assumptions either has an exact triple factor, or a nonzero
ORIGINAL quadratic transverse Hessian repair along a fixed tangent vector.

In the nontriple branch we split by a principal transverse cofactor of
the FULL four-by-four cubic Hessian on the actual pole quotient:

* If a cofactor survives, the already-proved kernel-line bridge forces
  isotropy of the nonzero quadratic transverse repair.
* Otherwise all transverse principal cofactors vanish.

The second alternative is deliberately not called "full rank two" yet:
excluding every full off-diagonal adjugate entry is a separate matrix
argument. We do not infer a contradiction from isotropy alone.
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

/-- A genuine source cubic pole either has an exact triple transverse
Hessian determinant, or its actual quadratic transverse repair is
nonzero and the full cubic pole matrix satisfies a cofactor split.

On the cofactor branch, the same nonzero source tangent is isotropic
for the original quadratic Hessian. No kernel-line hypothesis or
source endpoint extractor is added. -/
theorem sourceCubic_genuinePole_detOne_isotropicRepair_or_noTransverseCofactor_or_exactTriple
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
        (B3 K ⧸ Ideal.span {p}) :=
      φ.mapMatrix (hessian L3)
    let T2 : Matrix (Fin 3) (Fin 3) K :=
      fun i j => (referenceSlice a
        (hessian L2 (.inr i) (.inr j))).coeff 0
    (∃ (ell : Fin 3 → K)
        (M : Matrix (Fin 3) (Fin 3) K) (r t : K),
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      M.det ≠ 0 ∧ (r ≠ 0 ∨ t ≠ 0) ∧
      let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
      (∃ i : Fin 3, (∑ j : Fin 3, T2 i j * w0 j) ≠ 0) ∧
      ((∃ k : Fin 3,
          A.adjugate (.inr k) (.inr k) ≠ 0 ∧
          (∑ i : Fin 3, ∑ j : Fin 3,
            w0 i * T2 i j * w0 j) = 0) ∨
        (∀ k : Fin 3, A.adjugate (.inr k) (.inr k) = 0)))
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
  let T2 : Matrix (Fin 3) (Fin 3) K :=
    fun i j => (referenceSlice a
      (hessian L2 (.inr i) (.inr j))).coeff 0
  obtain ⟨ell, M, r, t, hlin, hM, hrt,
      hWne, hAker, _htrace, ⟨i, hi⟩⟩ | htriple :=
    sourceCubic_genuinePole_detOne_transverseRepair_or_exactTriple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · let w0 : Fin 3 → K := M.mulVec ![(0 : K), r, t]
    have hresponse :=
      sourceCubic_quadraticTransverseRepair_quotient_eq_C
        F a p w0 i
    have hnonzero :
        (∑ j : Fin 3, T2 i j * w0 j) ≠ 0 := by
      intro hz
      apply hi
      rw [hresponse, hz]
      simp
    refine Or.inl ⟨ell, M, r, t, hlin, hM, hrt,
      ⟨i, hnonzero⟩, ?_⟩
    by_cases hcof :
        ∃ k : Fin 3, A.adjugate (.inr k) (.inr k) ≠ 0
    · obtain ⟨k, hkk⟩ := hcof
      left
      refine ⟨k, hkk, ?_⟩
      exact
        sourceCubic_rankThreePoleKernel_quadraticTransverse_isotropic_of_cofactor
          F a p ell hlin hp hcap hdetOne w0 k
          hWne hAker hkk
    · right
      intro k
      by_contra hk
      exact hcof ⟨k, hk⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
