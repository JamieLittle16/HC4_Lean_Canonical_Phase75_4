import HC4.Polynomial.RankThreeCubicRepeatedFactor
import HC4.Polynomial.RankThreeCubicPoleCofactor
import Mathlib

/-!
# Unified source-honest pole trichotomy for full-rank cubic transverse cap

The actual cubic source has either:
1. a constant-linear rational characteristic;
2. a repeated irreducible degree-one factor of its transverse Hessian
   determinant at the selected source slice; or
3. on one irreducible factor, both a nonzero transverse Hessian kernel
   in the residue quotient and a nonzero adjugate cofactor.

The two pole cases still require geometric contradictions.  This is
not a proof of cap-three injectivity or HC4.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- A concrete, source-derived algebraic classification of the
full-rank cubic characteristic, without additional rank/pole/squarefree
or degree assumptions. -/
theorem exists_sourceCubic_linear_or_repeatedLinear_or_residueCofactor
    (F : MvPolynomial (Unit ⊕ Fin 3) K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (htrans : ((hessian (initialForm transverseCubicWeight 3 F)).submatrix
        Sum.inr Sum.inr).det ≠ 0) :
    let L := initialForm transverseCubicWeight 3 F
    ∃ (a : K) (V : Unit ⊕ Fin 3 → FractionRing (B3 K)),
      (sourceTransverseHessian a L).det ≠ 0 ∧
      V (.inl ()) = 1 ∧
      ((sourceTransverseHessian a L).map
          (algebraMap (B3 K) (FractionRing (B3 K))) *ᵥ
            (fun j : Fin 3 => V (.inr j)) =
        fun i : Fin 3 =>
          algebraMap (B3 K) (FractionRing (B3 K))
            (sourceNegativeMixedHessian a L i)) ∧
      ((∃ N : Matrix (Fin 3) (Fin 3) K,
          ∀ i : Fin 3,
            V (.inr i) =
              algebraMap (B3 K) (FractionRing (B3 K))
                (∑ j : Fin 3, MvPolynomial.C (N i j) * X j))
        ∨ (∃ p : B3 K, Irreducible p ∧
            p * p ∣ (sourceTransverseHessian a L).det ∧
            p.totalDegree = 1)
        ∨ (∃ p : B3 K, Irreducible p ∧
            p ∣ (sourceTransverseHessian a L).det ∧
            (∃ S : Fin 3 → (B3 K ⧸ Ideal.span {p}),
              S ≠ 0 ∧
              ((sourceTransverseHessian a L).map
                (Ideal.Quotient.mk (Ideal.span {p}))) *ᵥ S = 0) ∧
            (∃ i j : Fin 3, ¬ p ∣
              (sourceTransverseHessian a L).adjugate i j))) := by
  obtain ⟨a, V, hreg, hlong, heq, hcase⟩ :=
    exists_sourceCubic_linear_or_nonsquarefree_or_residueCofactor
      F hcap hdet htrans
  refine ⟨a, V, hreg, hlong, heq, ?_⟩
  rcases hcase with hlin | hnot | hcof
  · exact Or.inl hlin
  · exact Or.inr (Or.inl
      (exists_sourceCubic_repeated_linear_factor a F hreg hnot))
  · exact Or.inr (Or.inr hcof)

end
end HC4.Polynomial.RankThreeCubic
