import Mathlib.Tactic

/-!
# Extending a fixed binary tangent kernel through normal cofactors

For a symmetric 3x3 matrix over an integral domain, write its
last 2x2 tangential block as Q. If a vector (r,t) is in the
kernel of Q and the normal first row of the adjugate vanishes,
then either Q is identically zero, or the *full* matrix
annihilates (0,r,t).

The first case genuinely matters: when Q=0, the full Hessian may
have rank two and a moving tangent kernel. It cannot simply be
discarded by a nonzero determinant hypothesis.

The proof is a finite cofactor calculation, without fractions,
generic points, or division by a chosen minor.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- A normal-adjugate row zero and a constant tangential kernel
yield a full tangent kernel, unless the tangential block itself
vanishes. There is no rank assumption on the full matrix. -/
theorem symmetricThree_tangentKernel_full_or_tangentBlockZero
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (hSym : H.IsSymm)
    (hN01 : H.adjugate 0 1 = 0)
    (hN02 : H.adjugate 0 2 = 0)
    (r t : R)
    (hQ1 : H 1 1 * r + H 1 2 * t = 0)
    (hQ2 : H 2 1 * r + H 2 2 * t = 0) :
    (H 1 1 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0) ∨
      (H 0 1 * r + H 0 2 * t = 0) := by
  classical
  have h21 : H 2 1 = H 1 2 := hSym.apply 1 2
  have h01 : H 0 2 * H 1 2 - H 0 1 * H 2 2 = 0 := by
    simpa [Matrix.adjugate_fin_three, h21] using hN01
  have h02 : H 0 1 * H 1 2 - H 0 2 * H 1 1 = 0 := by
    simpa [Matrix.adjugate_fin_three] using hN02
  have hQ2' : H 1 2 * r + H 2 2 * t = 0 := by
    simpa only [h21] using hQ2
  let w : R := H 0 1 * r + H 0 2 * t
  by_cases hd : H 1 1 = 0
  · by_cases he : H 1 2 = 0
    · by_cases hf : H 2 2 = 0
      · exact Or.inl ⟨hd, he, hf⟩
      · right
        have hfw : H 2 2 * w = 0 := by
          dsimp [w]
          linear_combination (H 0 2) * hQ2' - r * h01
        exact (mul_eq_zero.mp hfw).resolve_left hf
    · right
      have hew : H 1 2 * w = 0 := by
        dsimp [w]
        linear_combination (H 0 1) * hQ2' + t * h01
      exact (mul_eq_zero.mp hew).resolve_left he
  · right
    have hdw : H 1 1 * w = 0 := by
      dsimp [w]
      linear_combination (H 0 1) * hQ1 - t * h02
    exact (mul_eq_zero.mp hdw).resolve_left hd

end
end HC4.Polynomial.RankThreeCubic
