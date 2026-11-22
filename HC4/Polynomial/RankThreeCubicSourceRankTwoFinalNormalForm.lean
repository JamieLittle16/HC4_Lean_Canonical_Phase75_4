import HC4.Polynomial.RankThreeCubicSourceUnconditionalRankTwoTransport
import HC4.Polynomial.RankThreeCubicSourceExactPoleDegree
import Mathlib.Tactic

/-!
# Source cubic dichotomy: linear velocity or one forced rank-two pole

The actual cubic source classification has only two alternatives:
(1) its transverse characteristic is constant-linear, or
(2) it has a genuine unique repeated degree-one denominator pole.

Rank-one elimination now makes the second alternative *necessarily*
a principal rank-two hyperplane, with the normalized source residue
aligned to the principal adjugate and subject to all characteristic-
time cofactor contraction identities.

This theorem assembles those results with the same original
constant-Hessian-determinant and transverse-regularity assumptions.
It is a stronger normal form for the residual rank-two obstruction;
it does not assume or prove that the rank-two case is impossible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The full source cubic can be reduced to its constant-linear
characteristic or a single *rank-two* genuine repeated linear
pole carrying a nonzero aligned residue and all-time cofactor
transport. No extra chosen Schur pivot is required. -/
theorem exists_sourceCubic_linear_or_uniqueRankTwoPole_allTimeTransport
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
      Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → F3 K),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      (∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V (pderiv i L) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (F3 K)) *ᵥ
            (fun i : Fin 3 => V (.inr i)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (F3 K) (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (F3 K)
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨
        ∃ (j : Fin 3) (p c : B3 K)
          (k : Fin 3) (s : B3 K) (T : Fin 3 → B3 K),
          Irreducible p ∧
          (sourceTransverseHessian a L).det = (p * p) * c ∧
          c ≠ 0 ∧
          p.totalDegree = 1 ∧
          c.totalDegree = 1 ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j)) ∧
          (¬ p ∣ (sourceTransverseHessian a L).adjugate k k) ∧
          p ∣ s ∧
          (∀ l : Fin 3,
            algebraMap (B3 K) (F3 K) (T l) =
              algebraMap (B3 K) (F3 K) s * V (.inr l)) ∧
          let H := sourceTransverseHessian a L
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
                  (Q l m).coeff n * H.adjugate l m))) ∧
          (∀ (u : Fin 3) (v : B3 K),
            Irreducible v →
            v ∣ (IsFractionRing.den (B3 K) (V (.inr u)) : B3 K) →
            ¬ v ∣ IsFractionRing.num (B3 K) (V (.inr u)) →
            Associated v p)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  obtain ⟨a, V, hregular, hV, hgrad, hker, hcase⟩ :=
    exists_sourceCubic_linear_or_singleGenuinePole_exactCofactor
      F hcap hdet htrans
  refine ⟨a, V, hregular, hV, hgrad, hker, ?_⟩
  rcases hcase with hlin | ⟨j, p, c, hp, hfact, hc0, hpdeg, hcdeg, hpd, hpn, huniq⟩
  · exact Or.inl hlin
  · obtain ⟨k, s, T, hk, hps, hscale, hSk, hSker, halign, htime⟩ :=
      sourceCubic_genuinePole_unconditionalRankTwo_allTimeContractions
        F a V hV hgrad hregular j p hp hpd hpn
    exact Or.inr
      ⟨j, p, c, k, s, T,
        hp, hfact, hc0, hpdeg, hcdeg, hpd, hpn, hk,
        hps, hscale, hSk, hSker, halign, htime, huniq⟩

end
end HC4.Polynomial.RankThreeCubic
