import HC4.Polynomial.RankThreeCubicSourceUnconditionalRankTwoTransport
import Mathlib.Tactic

/-!
# Polarise all source cofactor transport constraints

The source cubic's normalized rank-two pole supplies one cofactor
contraction for every transverse derivative index i and every
characteristic time coefficient n.

Taking the transverse Euler polarisation of those third-derivative
coefficients gives a matrix-valued linear form

  E_n(l,m) = sum_i X_i * Q_i(l,m).coeff(n).

The complete cofactor contraction of E_n is therefore divisible by
the genuine pole prime, for every n. This assembles the source
transport identities in a matrix-geometric form suitable for
comparing with longitudinal Hessian perturbations. No equality to
a determinant perturbation is assumed here.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- All three source cofactor contractions combine into the
cofactor contraction of their transverse-linear polarisation.
This is valid over the original polynomial ring, without passing
to a fraction field or introducing a pivot assumption. -/
theorem cofactorContraction_dvd_of_transversePolarization
    (H : Matrix (Fin 3) (Fin 3) (B3 K))
    (p : B3 K)
    (Q : Fin 3 → Fin 3 → Fin 3 → B3 K)
    (hQ : ∀ i : Fin 3,
      p ∣ (∑ l : Fin 3, ∑ m : Fin 3,
        Q i l m * H.adjugate l m)) :
    p ∣ (∑ l : Fin 3, ∑ m : Fin 3,
      (∑ i : Fin 3,
        (MvPolynomial.X i : B3 K) * Q i l m) *
          H.adjugate l m) := by
  classical
  have hrearrange :
      (∑ l : Fin 3, ∑ m : Fin 3,
        (∑ i : Fin 3, (MvPolynomial.X i : B3 K) * Q i l m) *
          H.adjugate l m) =
      ∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
        (∑ l : Fin 3, ∑ m : Fin 3, Q i l m * H.adjugate l m) := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hrearrange]
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right (hQ i) _

/-- A genuine pole now admits a *single coherent family* of source
triple-transverse-derivative time polynomials whose polarised
cofactor contraction is divisible by p at every time coefficient.

The principal rank-two pivot and all residue properties are still
derived entirely from the source, not supplied as hypotheses. -/
theorem sourceCubic_genuinePole_polarizedTimeCofactorConstraints
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
    ∃ (k : Fin 3) (s : B3 K) (T : Fin 3 → B3 K)
      (Q : Fin 3 → Fin 3 → Fin 3 → _root_.Polynomial (B3 K)),
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
      (∀ i l m : Fin 3,
        (Q i l m).map (algebraMap (B3 K) (F3 K)) =
          lineEval (transverseGenericPoint a) V
            (pderiv (.inr m) (pderiv (.inr l)
              (pderiv (.inr i) L)))) ∧
      (∀ n : ℕ, ∀ i : Fin 3,
        p ∣ (∑ l : Fin 3, ∑ m : Fin 3,
          (Q i l m).coeff n * H.adjugate l m)) ∧
      (∀ n : ℕ,
        p ∣ (∑ l : Fin 3, ∑ m : Fin 3,
          (∑ i : Fin 3, (MvPolynomial.X i : B3 K) *
            (Q i l m).coeff n) * H.adjugate l m)) := by
  classical
  let L : SB K := initialForm transverseCubicWeight 3 F
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  obtain ⟨k, s, T, hk, hps, hscale, hSk, hSker, halign, htime⟩ :=
    sourceCubic_genuinePole_unconditionalRankTwo_allTimeContractions
      F a V hV hgrad hregular j p hp hpd hpn
  choose Q hQ hdiv using htime
  refine ⟨k, s, T, Q, hk, hps, hscale,
    hSk, hSker, halign, ?_, ?_, ?_⟩
  · intro i l m
    exact hQ i l m
  · intro n i
    exact hdiv i n
  · intro n
    exact cofactorContraction_dvd_of_transversePolarization
      H p (fun i l m => (Q i l m).coeff n) (fun i => hdiv i n)

end
end HC4.Polynomial.RankThreeCubic
