import HC4.Polynomial.RankThreeCubicSourceSinglePoleNonzeroResidue
import Mathlib.Tactic

/-!
# Source cubic repeated-pole rank split on the one pole hyperplane

The actual source transverse Hessian is symmetric. For its
irreducible determinant factor p, the rank of the matrix modulo p
is at most two. It has a rank-two principal Schur pivot exactly
when some diagonal cofactor survives.

If no principal cofactor survives, the symmetry/adjugate identities
force every cofactor to vanish; this is the rank-at-most-one branch.

This is an exhaustive source-honest algebraic split and does not
assert that either branch is impossible.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- On a prime component of the *actual source* Hessian determinant,
either all 2x2 cofactors vanish, or one principal cofactor survives.

In the fraction field of K[y]/(p), these are precisely the
rank-at-most-one and rank-two alternatives for a singular 3x3 Hessian. -/
theorem sourceCubic_primeHessian_rankOne_or_principalRankTwo
    (a : K) (L : SB K)
    (p : B3 K)
    (hp : Irreducible p)
    (hpdet : p ∣ (sourceTransverseHessian a L).det) :
    (∀ i j : Fin 3,
      p ∣ (sourceTransverseHessian a L).adjugate i j) ∨
    (∃ k : Fin 3,
      ¬ p ∣ (sourceTransverseHessian a L).adjugate k k) := by
  classical
  let H : Matrix (Fin 3) (Fin 3) (B3 K) :=
    sourceTransverseHessian a L
  by_cases hall : ∀ i j : Fin 3, p ∣ H.adjugate i j
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨i, j, hij⟩ := hall
    exact exists_principal_cofactor_not_dvd
      H (sourceTransverseHessian_isSymm a L)
      p hp.prime hpdet ⟨i, j, hij⟩

end
end HC4.Polynomial.RankThreeCubic
