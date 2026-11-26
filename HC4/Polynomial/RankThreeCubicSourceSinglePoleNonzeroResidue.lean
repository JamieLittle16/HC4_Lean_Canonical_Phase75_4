module

public import HC4.Polynomial.RankThreeCubicSourceGenuinePoleResidue
public import HC4.Polynomial.RankThreeCubicSourceExactPoleDegree
public import Mathlib.Tactic

/-!
# Full-rank cubic source: linear transport or a nonzero normalized pole residue

The genuine pole is singled out by the already-green source cubic
classification. The common denominator and its nonzero prime residue
are constructed from the reduced denominators, with no independent
normalization, rank, or pole-order hypothesis.

The nonlinear branch retains:
* det(H) = p²*c with irreducible p and both factors of degree one;
* an actual reduced denominator factor p of a transverse velocity;
* one normalized polynomial vector T and common denominator s;
* the nonzero residue S = T mod p killed by H mod p;
* all source gradient quadratic time-coefficient identities on S;
* uniqueness of the denominator prime up to association.

This theorem does not claim the remaining singular direction is
impossible: that geometric exclusion remains a separate task.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicSourceSinglePoleNonzeroResidue

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicSourceSinglePoleNonzeroResidue

open RankThreeCubicSourceSinglePoleNonzeroResidue (B3 F3 SB)

theorem exists_sourceCubic_linear_or_singlePole_nonzeroQuadraticResidue
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
        (∃ (j : Fin 3) (p c s : B3 K) (T : Fin 3 → B3 K),
          Irreducible p ∧
          (sourceTransverseHessian a L).det = (p * p) * c ∧
          c ≠ 0 ∧
          p.totalDegree = 1 ∧
          c.totalDegree = 1 ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j)) ∧
          p ∣ s ∧
          (∀ k : Fin 3,
            algebraMap (B3 K) (F3 K) (T k) =
              algebraMap (B3 K) (F3 K) s * V (.inr k)) ∧
          let H := sourceTransverseHessian a L
          let q : B3 K →+* (B3 K ⧸ Ideal.span {p}) :=
            Ideal.Quotient.mk (Ideal.span {p})
          let S : Fin 3 → (B3 K ⧸ Ideal.span {p}) :=
            fun k => q (T k)
          S ≠ 0 ∧
          (H.map q) *ᵥ S = 0 ∧
          (∀ i : Fin 3,
            ∃ Q : Fin 3 → Fin 3 → _root_.Polynomial (B3 K),
              (∀ k l : Fin 3,
                (Q k l).map (algebraMap (B3 K) (F3 K)) =
                  lineEval (transverseGenericPoint a) V
                    (pderiv (.inr l) (pderiv (.inr k)
                      (pderiv (.inr i) L)))) ∧
              (∀ n : ℕ,
                (∑ k : Fin 3, ∑ l : Fin 3,
                  q ((Q k l).coeff n) * S k * S l) = 0)) ∧
          (∀ (k : Fin 3) (u : B3 K),
            Irreducible u →
            u ∣ (IsFractionRing.den (B3 K) (V (.inr k)) : B3 K) →
            ¬ u ∣ IsFractionRing.num (B3 K) (V (.inr k)) →
            Associated u p))) := by
  classical
  obtain ⟨a, V, hreg, hV, hgrad, hker, hcase⟩ :=
    exists_sourceCubic_linear_or_singleGenuinePole_exactCofactor
      F hcap hdet htrans
  refine ⟨a, V, hreg, hV, hgrad, hker, ?_⟩
  rcases hcase with hlin | ⟨j, p, c, hp, hfact, hc0, hpdeg, hcdeg, hpd, hpn, huniq⟩
  · exact Or.inl hlin
  · obtain ⟨s, T, hps, hscale, hS, hSker, hquad⟩ :=
      sourceCubic_genuinePole_nonzeroNormalizedQuadraticResidue
        F a V hV hgrad j p hp hpd
    exact Or.inr
      ⟨j, p, c, s, T, hp, hfact, hc0, hpdeg, hcdeg,
        hpd, hpn, hps, hscale, hS, hSker, hquad, huniq⟩

end
end HC4.Polynomial.RankThreeCubic
