import HC4.Polynomial.RankThreeCubicSourceRankTwoAdaptedFrame
import Mathlib.Tactic

/-!
# A repeated determinant factor constrains Hessian kernel trajectories

This is the algebraic geometric core of the rank-two repeated-pole
direction argument.

Let H be a matrix-valued additive function of the transverse point,
and suppose det(H(v)) = p(v)^2*c(v), with p,c additive linear
functionals. If a nonzero vector S is killed by both H(x) and H(S),
where p(x)=0, then the two determinants at S and x+S vanish.

The factorization immediately yields

  p(S)^2 * c(x) = 0.

Over an integral domain this is the dichotomy
  p(S) = 0  or  c(x) = 0.

Thus on the generically exactly-double pole component (c(x)!=0),
the kernel direction S is forced to be tangent to the pole.
The same calculation isolates the possible triple-pole residue
without assuming it away.

This theorem does not yet establish that an actual source
residue is killed by H(S); that comes from the full cubic
third-derivative symmetry and source quadratic transport.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- Two singular Hessian matrices with one common nonzero kernel
force their repeated determinant factor's kernel direction
to lie in the pole, unless the residual factor also vanishes
at the original point. No invertibility assumptions are used. -/
theorem additivePencil_repeatedPole_kernel_tangent_or_cofactor_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (H : (Fin 3 → R) → Matrix (Fin 3) (Fin 3) R)
    (p c : (Fin 3 → R) → R)
    (hHadd : ∀ u v, H (u + v) = H u + H v)
    (hpadd : ∀ u v, p (u + v) = p u + p v)
    (hcadd : ∀ u v, c (u + v) = c u + c v)
    (hfactor : ∀ v, (H v).det = p v * p v * c v)
    (x S : Fin 3 → R)
    (k : Fin 3) (hSk : S k ≠ 0)
    (hpx : p x = 0)
    (hHx : (H x) *ᵥ S = 0)
    (hHS : (H S) *ᵥ S = 0) :
    p S = 0 ∨ c x = 0 := by
  classical
  have hk : S k ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ne_zero hSk
  have hdetS : (H S).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hHS hk
  have hsum : (H (x + S)) *ᵥ S = 0 := by
    rw [hHadd, Matrix.add_mulVec, hHx, hHS, zero_add]
  have hdetSum : (H (x + S)).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hsum hk
  have hz1 : p S * p S * c S = 0 := by
    rw [← hfactor S]
    exact hdetS
  have hz2 : p S * p S * (c x + c S) = 0 := by
    have h := hfactor (x + S)
    rw [hdetSum, hpadd, hcadd, hpx, zero_add] at h
    exact h.symm
  have hz : (p S * p S) * c x = 0 := by
    calc
      (p S * p S) * c x =
          p S * p S * (c x + c S) - p S * p S * c S := by ring
      _ = 0 := by rw [hz2, hz1, sub_self]
  rcases mul_eq_zero.mp hz with hp2 | hc
  · left
    rcases mul_eq_zero.mp hp2 with hp0 | hp0
    · exact hp0
    · exact hp0
  · exact Or.inr hc

/-- In the exactly-double case (the complementary linear factor
does not vanish on the pole plane), the Hessian kernel line is
necessarily tangent to the pole. -/
theorem additivePencil_exactDoublePole_kernel_tangent
    {R : Type*} [CommRing R] [IsDomain R]
    (H : (Fin 3 → R) → Matrix (Fin 3) (Fin 3) R)
    (p c : (Fin 3 → R) → R)
    (hHadd : ∀ u v, H (u + v) = H u + H v)
    (hpadd : ∀ u v, p (u + v) = p u + p v)
    (hcadd : ∀ u v, c (u + v) = c u + c v)
    (hfactor : ∀ v, (H v).det = p v * p v * c v)
    (x S : Fin 3 → R)
    (k : Fin 3) (hSk : S k ≠ 0)
    (hpx : p x = 0)
    (hCx : c x ≠ 0)
    (hHx : (H x) *ᵥ S = 0)
    (hHS : (H S) *ᵥ S = 0) :
    p S = 0 := by
  rcases additivePencil_repeatedPole_kernel_tangent_or_cofactor_zero
      H p c hHadd hpadd hcadd hfactor x S k hSk hpx hHx hHS with hpS | hcX
  · exact hpS
  · exact False.elim (hCx hcX)

end
end HC4.Polynomial.RankThreeCubic
