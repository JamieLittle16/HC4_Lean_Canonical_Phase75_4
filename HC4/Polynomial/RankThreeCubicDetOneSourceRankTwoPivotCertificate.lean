import HC4.Polynomial.RankThreeCubicDetOneSourceFullAdjugateRankSplit
import Mathlib.Tactic

/-!
# Genuine cubic pole: exact rank-two certificate from the actual source

The previous source-level classification obtained full-adjugate zero
in the low-rank branch. Here we retain simultaneously the EXISTING
surviving principal two-by-two minor of the ORIGINAL transverse
Hessian modulo the very same irreducible pole.

Hence this is an exact rank-two certificate over the fraction field
of the pole quotient, not just rank at most two. This pivot permits
a Schur-complement calculation after localization; it does not
assert that the cofactor is a unit in the original quotient ring.

The quadratic transverse repair remains explicitly nonzero.
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

/-- Every genuine cubic denominator pole of the determinant-one source
has an isotropic rank-three quadratic repair, an exact rank-two
full-cubic Hessian with surviving transverse pivot and nonzero
quadratic repair, or an exact triple transverse determinant pole.

No principal-minor witness is separately assumed. -/
theorem sourceCubic_genuinePole_detOne_isotropic_or_rankTwoPivot_or_exactTriple
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
        (A.adjugate = 0 ∧
          ∃ k : Fin 3, (H.map q).adjugate k k ≠ 0)))
    ∨
    (∃ lambda : K, lambda ≠ 0 ∧
      H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L3 : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L3
  let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
    Ideal.Quotient.mk (Ideal.span {p})
  obtain ⟨ell, M, r, t, hlin, hM, hrt,
      hrepair, hcase⟩ | htriple :=
    sourceCubic_genuinePole_detOne_isotropicRepair_or_fullAdjugateZero_or_exactTriple
      F a V hcap hdetOne hV hgrad hregular u p hp hpd hpn
  · refine Or.inl ⟨ell, M, r, t, hlin, hM, hrt, hrepair, ?_⟩
    rcases hcase with hiso | hzero
    · exact Or.inl hiso
    · right
      refine ⟨hzero, ?_⟩
      obtain ⟨k, hnot⟩ :=
        sourceCubic_genuinePole_has_principalRankTwo
          F a V hV hgrad hregular u p hp hpd hpn
      have hqCof : q (H.adjugate k k) ≠ 0 := by
        intro hz
        apply hnot
        exact Ideal.mem_span_singleton.mp
          (Ideal.Quotient.eq_zero_iff_mem.mp hz)
      have hmap : (H.map q).adjugate = H.adjugate.map q :=
        (q.map_adjugate H).symm
      refine ⟨k, ?_⟩
      rw [hmap]
      exact hqCof
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
