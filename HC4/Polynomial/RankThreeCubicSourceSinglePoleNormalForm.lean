import HC4.Polynomial.RankThreeCubicUniqueGenuinePole
import Mathlib.Tactic

/-!
# Source-normalized single hyperplane for a genuine cubic pole

The verified squarefree obstruction, local repeated-factor forcing,
and the cubic degree-three bound combine to show that any
non-polynomial full-rank source cubic characteristic has a unique
irreducible reduced denominator pole class.

We retain the actual longitudinal anchor, full gradient transport,
fractional Hessian equation, and the factorization det(H) = p² * c
with totalDegree(c) ≤ 1. Nothing in this statement asserts the
remaining pole is impossible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- Source-honest cubic dichotomy with a fixed prime hyperplane:
linear velocity, or a genuine repeated denominator pole p such that
every other irreducible reduced-denominator pole is associated to p. -/
theorem exists_sourceCubic_linear_or_singleGenuinePole
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
        (∃ (j : Fin 3) (p c : B3 K),
          Irreducible p ∧
          (sourceTransverseHessian a L).det = (p * p) * c ∧
          c ≠ 0 ∧ c.totalDegree ≤ 1 ∧
          p.totalDegree = 1 ∧
          p ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K) ∧
          ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr j)) ∧
          (∀ (k : Fin 3) (q : B3 K),
            Irreducible q →
            q ∣ (IsFractionRing.den (B3 K) (V (.inr k)) : B3 K) →
            ¬ q ∣ IsFractionRing.num (B3 K) (V (.inr k)) →
            Associated q p))) := by
  classical
  obtain ⟨a, V, hreg, hV, hgrad, hker, hcase⟩ :=
    exists_sourceCubic_linear_or_repeatedGenuinePole_withCofactor
      F hcap hdet htrans
  refine ⟨a, V, hreg, hV, hgrad, hker, ?_⟩
  rcases hcase with hlin | ⟨j, p, c, hp, hfact, hc0, hcdeg, hpdeg, hpd, hpn⟩
  · exact Or.inl hlin
  · refine Or.inr ⟨j, p, c, hp, hfact, hc0, hcdeg,
      hpdeg, hpd, hpn, ?_⟩
    intro k q hq hqd hqn
    exact (sourceCubic_genuinePole_primes_associated
      F a V hV hgrad hreg j k p q
      hp hq hpd hpn hqd hqn).symm

end
end HC4.Polynomial.RankThreeCubic
