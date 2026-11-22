import HC4.Polynomial.RankThreeCubicSourceLongitudinalPoleResidue
import Mathlib.Tactic

/-!
# Source-honest full cubic Hessian tangent kernel along a genuine double pole

The source-derived fixed tangent direction W has already been proved
to annihilate the three transverse Hessian rows along the genuine
pole plane. This file uses the *same* normalized residue S and
the *fourth (longitudinal)* row of the original gradient transport.

The longitudinal row annihilates S modulo p after clearing its actual
polynomial denominator s. Because S is aligned with W at a surviving
principal rank-two cofactor pivot, it also annihilates W modulo p.
This is an exact divisibility statement in the original transverse
polynomial ring, not an additional kernel assumption.

Consequently the nontriple source pole has a fixed tangent direction
that is a kernel of the *full* cubic source Hessian on the pole plane.
The exact scalar triple pole remains an explicit alternative.

This does NOT imply the full Hessian of F has a kernel: its strictly
lower transverse-degree components may repair the cubic-face kernel.
The determinant-one condition will constrain that repair.
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

/-- An actual rank-two cubic characteristic pole has a fixed tangent
kernel of its full cubic-source Hessian on the pole plane, or an
exact nonzero scalar triple Hessian factor. The same source frame,
same denominator and same normalized nonzero residue are retained. -/
theorem sourceCubic_genuinePole_fullHessianFixedTangent_or_exactTriple
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
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
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    let b : Fin 3 → B3 K :=
      fun i => referenceSlice a
        (pderiv (.inr i) (pderiv (.inl ()) L))
    ∃ (ell : Fin 3 → K) (k : Fin 3),
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      (¬ p ∣ H.adjugate k k) ∧
      ((∃ (M : Matrix (Fin 3) (Fin 3) K) (r t : K)
          (s : B3 K) (T : Fin 3 → B3 K),
          M.det ≠ 0 ∧
          (∑ i : Fin 3, ell i * M i 1) = 0 ∧
          (∑ i : Fin 3, ell i * M i 2) = 0 ∧
          (r ≠ 0 ∨ t ≠ 0) ∧
          (∀ x y : K,
            let A := H.map (MvPolynomial.aeval
              (M.mulVec ![(0 : K), x, y])).toRingHom
            (M.transpose * A * M) *ᵥ ![(0 : K), r, t] = 0) ∧
          p ∣ s ∧
          (∀ i : Fin 3,
            algebraMap (B3 K) (F3 K) (T i) =
              algebraMap (B3 K) (F3 K) s * V (.inr i)) ∧
          (let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
              Ideal.Quotient.mk (Ideal.span {p})
           let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
              fun i => q (MvPolynomial.C
                ((M.mulVec ![(0 : K), r, t]) i))
           q (T k) ≠ 0 ∧
           (∀ i : Fin 3, q (T i) * W k = W i * q (T k)) ∧
           p ∣ ∑ i : Fin 3, b i *
             MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) i)))
       ∨
       ∃ lambda : K, lambda ≠ 0 ∧
         H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  let b : Fin 3 → B3 K :=
    fun i => referenceSlice a
      (pderiv (.inr i) (pderiv (.inl ()) L))
  obtain ⟨ell, k, hpoly, hk, hbranch⟩ :=
    sourceCubic_genuineRankTwo_residue_alignedFixedTangent_or_exactTriple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  rcases hbranch with
      ⟨M, r, t, s, T, hM, hM1, hM2, hrt,
        hframe, hps, hscale, hSk, hcross⟩ | htriple
  · left
    let R := B3 K ⧸ Ideal.span {p}
    let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
    let S : Fin 3 → R := fun i => q (T i)
    let W : Fin 3 → R := fun i =>
      q (MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) i))
    letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
      (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
    have hrowDiv : p ∣ ∑ i : Fin 3, b i * T i :=
      sourceCubic_normalizedPole_longitudinalMixedRow_divisible
        F a V hV hgrad p s hps T hscale
    have hrowQ : (∑ i : Fin 3, q (b i) * S i) = 0 := by
      have hqzero : q (∑ i : Fin 3, b i * T i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton.mpr hrowDiv)
      simpa only [map_sum, map_mul] using hqzero
    have hWrow : (∑ i : Fin 3, q (b i) * W i) = 0 :=
      fixedTangent_mixedRow_zero_of_alignedResidue
        (fun i => q (b i)) S W k hSk hcross hrowQ
    have hWdiv : p ∣ ∑ i : Fin 3,
        b i * MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) i) := by
      have hqzero : q (∑ i : Fin 3,
          b i * MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) i)) = 0 := by
        simpa only [map_sum, map_mul] using hWrow
      exact Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hqzero)
    exact ⟨M, r, t, s, T, hM, hM1, hM2, hrt,
      hframe, hps, hscale, hSk, hcross, hWdiv⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
