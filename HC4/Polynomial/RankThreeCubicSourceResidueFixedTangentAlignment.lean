import HC4.Polynomial.RankThreeCubicSourceFullTangentKernelOrTriple
import HC4.Polynomial.RankThreeCubicFixedKernelResidueLift
import HC4.Polynomial.RankThreeCubicResidueKernelDirection
import HC4.Polynomial.RankThreeCubicSourceRankTwoAdjugateAlignment
import Mathlib.Tactic

/-!
# The actual source pole residue aligns with the fixed full tangent kernel

In the non-triple genuine pole branch, the source cubic has a
fixed tangent vector W=M(0,r,t) killed by the full Hessian
along p=0. Homogeneity one lifts the vanishing to the
polynomial divisibility p | H(y)W; thus the *constant* vector
W is a kernel vector of H modulo p.

The genuine source gradient transport separately produces
the denominator-normalised residue S=q(T), nonzero at a
principal rank-two cofactor pivot k. Both W and S lie in
the kernel of the same rank-two matrix over K[y]/(p), so
their cross-products vanish:

  S_i W_k = W_i S_k,  for every i.

The polynomial normalisation p | s and s*V=T is retained,
making this a statement about the actual rational source
characteristic, not an independently chosen kernel vector.

This is a geometric alignment theorem, not an exclusion
of the nontriple pole. The source's next nontrivial
constraint must control the scalar along the fixed line.
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

/-- A genuine source cubic pole either has scalar triple
Hessian determinant, or its actual normalised denominator
residue is collinear modulo p with a constant, nonzero
source-derived tangent kernel direction. -/
theorem sourceCubic_genuineRankTwo_residue_alignedFixedTangent_or_exactTriple
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
    let H := sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)
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
          p ∣ s ∧
          (∀ l : Fin 3,
            algebraMap (B3 K) (F3 K) (T l) =
              algebraMap (B3 K) (F3 K) s * V (.inr l)) ∧
          (let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
              Ideal.Quotient.mk (Ideal.span {p})
           let W : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
              fun i => q (MvPolynomial.C
                ((M.mulVec ![(0 : K), r, t]) i))
           q (T k) ≠ 0 ∧
             ∀ i : Fin 3, q (T i) * W k = W i * q (T k)))
       ∨
       ∃ lambda : K, lambda ≠ 0 ∧
         H.det = MvPolynomial.C lambda * (p * p * p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨ell, k, hpoly, hk, hbranch⟩ :=
    sourceCubic_genuineRankTwo_fullTangentKernel_or_exactTriple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨ell, k, hpoly, hk, ?_⟩
  rcases hbranch with ⟨M, r, t, hM, hM1, hM2, hrt, hfull⟩ | htriple
  · left
    obtain ⟨s, T, hps, hscale, hSk, hSker, halign, hquad⟩ :=
      sourceCubic_genuinePole_rankTwo_adjugateAlignedResidue
        F a V hV hgrad u p hp hpd hpn k hk
    let R := B3 K ⧸ Ideal.span {p}
    let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
    let W : Fin 3 → R := fun i =>
      q (MvPolynomial.C ((M.mulVec ![(0 : K), r, t]) i))
    let S : Fin 3 → R := fun i => q (T i)
    letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
      (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
    have hell : ell ≠ 0 := by
      intro he
      apply hp.ne_zero
      rw [hpoly, he]
      simp
    have hhom (i j : Fin 3) : (H i j).IsHomogeneous 1 :=
      sourceCubic_transverseHessian_homogeneous_one a F i j
    have hframe (x y : K) :
        let A := H.map (MvPolynomial.aeval
          (M.mulVec ![(0 : K), x, y])).toRingHom
        (M.transpose * A * M) *ᵥ ![(0 : K), r, t] = 0 := by
      funext i
      have h := hfull x y
      fin_cases i
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h.1
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h.2.1
      · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h.2.2
    have hWker : (H.map q) *ᵥ W = 0 :=
      homogeneousLinearMatrix_fixedTangentKernel_modPole
        H hhom p ell hpoly hell M hM hM1 hM2 r t hframe
    have hpp : p * p ∣ H.det :=
      sourceCubic_genuinePole_is_repeatedFactor
        F a V hV hgrad u p hp hpd hpn
    have hpdet : p ∣ H.det := by
      obtain ⟨c, hc⟩ := hpp
      refine ⟨p * c, ?_⟩
      calc
        H.det = (p * p) * c := hc
        _ = p * (p * c) := by ring
    have hdet : (H.map q).det = 0 := by
      have hqdet : q H.det = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton.mpr hpdet)
      simpa only [RingHom.map_det] using hqdet
    have hcof' : q (H.adjugate k k) ≠ 0 := by
      intro hz
      exact hk
        (Ideal.mem_span_singleton.mp
          (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    have hmap : (H.map q).adjugate = H.adjugate.map q :=
      (q.map_adjugate H).symm
    have hcof : (H.map q).adjugate k k ≠ 0 := by
      rw [hmap]
      exact hcof'
    have hcross : ∀ i : Fin 3,
        S i * W k = W i * S k :=
      principalCofactor_twoKernelVectors_crossMultiply
        (H.map q) S W hSker hWker hdet k hcof
    refine ⟨M, r, t, s, T, hM, hM1, hM2, hrt, hps, hscale, ?_⟩
    exact ⟨hSk, hcross⟩
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
