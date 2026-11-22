import HC4.Polynomial.RankThreeCubicSourceRankOneElimination
import HC4.Polynomial.RankThreeCubicSourceAllTimeCofactorDivisibility
import Mathlib.Tactic

/-!
# Unconditional principal rank-two transport for a genuine cubic source pole

The actual cubic source's genuine reduced denominator prime cannot
support the rank-at-most-one residue geometry: the homogeneous
repeated-factor argument and cubic Hessian integrability force a
surviving principal cofactor.

We combine that result with the previously source-derived normalized
pole residue and its higher characteristic-time cofactor transport.
No rank-two pivot, residue vector, or further source condition is
assumed: all are derived from the same genuine denominator prime.

This is a sharpened *necessary condition* for the nonlinear
characteristic branch, not a terminal contradiction.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- An actual genuine cubic denominator pole automatically has a
surviving principal cofactor and a nonzero normalized residue aligned
with that principal adjugate column. For every source transverse
derivative and every characteristic-time coefficient the full
adjugate contraction vanishes modulo the same prime. -/
theorem sourceCubic_genuinePole_unconditionalRankTwo_allTimeContractions
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
    (j : Fin 3) (p : B3 K)
    (hp : Irreducible p)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j))) :
    let L := initialForm transverseCubicWeight 3 F
    let H := sourceTransverseHessian a L
    ∃ (k : Fin 3) (s : B3 K) (T : Fin 3 → B3 K),
      (¬ p ∣ H.adjugate k k) ∧
      p ∣ s ∧
      (∀ l : Fin 3,
        algebraMap (B3 K) (F3 K) (T l) =
          algebraMap (B3 K) (F3 K) s * V (.inr l)) ∧
      let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
        Ideal.Quotient.mk (Ideal.span {p})
      let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
        fun l => q (T l)
      S k ≠ 0 ∧
      (H.map q) *ᵥ S = 0 ∧
      (∀ i : Fin 3,
        q (H.adjugate k k) * S i =
          q (H.adjugate i k) * S k) ∧
      (∀ i : Fin 3,
        ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
          (∀ l m : Fin 3,
            (Q l m).map (algebraMap (B3 K) (F3 K)) =
              lineEval (transverseGenericPoint a) V
                (pderiv (.inr m) (pderiv (.inr l)
                  (pderiv (.inr i) L)))) ∧
          (∀ n : ℕ,
            p ∣ (∑ l : Fin 3, ∑ m : Fin 3,
              (Q l m).coeff n * H.adjugate l m))) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨k, hk⟩ :=
    sourceCubic_genuinePole_has_principalRankTwo
      F a V hV hgrad hregular j p hp hpd hpn
  obtain ⟨s, T, hps, hscale, hSk, hSker, halign, htime⟩ :=
    sourceCubic_rankTwo_genuinePole_allTime_cofactorContractions
      F a V hV hgrad j p hp hpd hpn k hk
  exact ⟨k, s, T, hk, hps, hscale, hSk, hSker, halign, htime⟩

end
end HC4.Polynomial.RankThreeCubic
