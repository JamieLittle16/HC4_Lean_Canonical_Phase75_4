import HC4.Polynomial.RankThreeCubicSourceRankTwoTangentOrTriple
import HC4.Polynomial.RankThreeCubicAdjugatePoleNormal
import Mathlib.Tactic

/-!
# Source cubic: normal adjugate annihilation or triple determinant pole

The actual rank-two pole has a normalized kernel residue aligned to
a nonvanishing principal adjugate column. The source's cubic transport
forces the residue either tangent to the repeated homogeneous linear
pole p or the complementary linear factor c divisible by p.

In the tangent case, the rank-one adjugate identities turn the
residue's normal orthogonality into a condition on *every* cofactor
column of the source Hessian:

  p | sum_i C(ell_i) * adj(H)(i,j)    for all j.

This is a polynomial divisibility condition, intrinsic to the actual
Hessian at its genuine denominator pole. It requires neither a
constant kernel direction nor an assumed Schur pivot.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- A genuine source cubic repeated denominator pole has either a
triple Hessian determinant factor or a normal covector annihilating
*all* adjugate columns modulo that prime. The normal is obtained
from the actual homogeneous linear pole equation. -/
theorem sourceCubic_genuineRankTwo_adjugateNormalZero_or_triple
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
    ∃ (c : B3 K) (ell : Fin 3 → K) (k : Fin 3),
      H.det = (p * p) * c ∧
      c ≠ 0 ∧
      p = ∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * MvPolynomial.C (ell i) ∧
      (¬ p ∣ H.adjugate k k) ∧
      ((∀ j : Fin 3,
          p ∣ (∑ i : Fin 3,
            MvPolynomial.C (ell i) * H.adjugate i j)) ∨ p ∣ c) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨k, c, s, T, ell,
      hfactor, hc0, hk, hps, hscale, hpoly,
      hres, hsplit⟩ :=
    sourceCubic_genuineRankTwo_residue_tangent_or_triple
      F a V hV hgrad hregular u p hp hpd hpn
  refine ⟨c, ell, k, hfactor, hc0, hpoly, hk, ?_⟩
  rcases hsplit with htangent | htriple
  · left
    let R := B3 K ⧸ Ideal.span {p}
    let q : B3 K →+* R := Ideal.Quotient.mk (Ideal.span {p})
    letI : (Ideal.span {p} : Ideal (B3 K)).IsPrime :=
      (Ideal.span_singleton_prime hp.ne_zero).2 hp.prime
    let S : Fin 3 → R := fun i => q (T i)
    obtain ⟨hSk, hSker, halign⟩ := hres
    have hpdet : p ∣ H.det := by
      refine ⟨p * c, ?_⟩
      rw [hfactor]
      ring
    have hqdet : q H.det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr hpdet)
    have hdet : (H.map q).det = 0 := by
      simpa only [RingHom.map_det] using hqdet
    have hcof' : q (H.adjugate k k) ≠ 0 := by
      intro hz
      exact hk
        (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    have hmap : (H.map q).adjugate = H.adjugate.map q :=
      (q.map_adjugate H).symm
    have hcof : (H.map q).adjugate k k ≠ 0 := by
      rw [hmap]
      exact hcof'
    have halign' (i : Fin 3) :
        (H.map q).adjugate k k * S i =
          (H.map q).adjugate i k * S k := by
      rw [hmap]
      exact halign i
    have hqTang : q (∑ i : Fin 3,
        MvPolynomial.C (ell i) * T i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr htangent)
    have htangent' :
        (∑ i : Fin 3, q (MvPolynomial.C (ell i)) * S i) = 0 := by
      simpa only [map_sum, map_mul] using hqTang
    have hn :
        ∀ j : Fin 3,
          (∑ i : Fin 3,
            q (MvPolynomial.C (ell i)) * (H.map q).adjugate i j) = 0 :=
      alignedTangentKernel_adjugateNormal_zero
        (H.map q) hdet S
        (fun i => q (MvPolynomial.C (ell i)))
        k hcof hSk halign' htangent'
    intro j
    have hqNormal : q (∑ i : Fin 3,
        MvPolynomial.C (ell i) * H.adjugate i j) = 0 := by
      calc
        q (∑ i : Fin 3,
            MvPolynomial.C (ell i) * H.adjugate i j) =
            ∑ i : Fin 3, q (MvPolynomial.C (ell i)) *
              q (H.adjugate i j) := by
                simp only [map_sum, map_mul]
        _ = 0 := by
          have h := hn j
          rw [hmap] at h
          exact h
    exact Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hqNormal)
  · exact Or.inr htriple

end
end HC4.Polynomial.RankThreeCubic
