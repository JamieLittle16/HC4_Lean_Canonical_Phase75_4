module

public import HC4.Polynomial.RankThreeCubicSourcePoleRankSplit
public import Mathlib.Tactic

/-!
# A principal cofactor fixes the nonzero coordinate of a singular kernel

For a singular three-by-three matrix over an integral domain, a
nonzero principal cofactor at index k makes the complementary
two-by-two block injective. Thus any nonzero kernel vector S
has S(k) nonzero. No localization or choice of basis is needed.

This is the missing denominator-normalized pivot certificate for
the rank-two branch of the cubic source pole analysis.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

private theorem two_by_two_kernel_zero_of_det_ne_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (a b c d x y : R)
    (hdet : a * d - b * c ≠ 0)
    (hrow₁ : a * x + b * y = 0)
    (hrow₂ : c * x + d * y = 0) :
    x = 0 ∧ y = 0 := by
  have hx : (a * d - b * c) * x = 0 := by
    calc
      (a * d - b * c) * x =
          d * (a * x + b * y) - b * (c * x + d * y) := by ring
      _ = 0 := by rw [hrow₁, hrow₂]; ring
  have hy : (a * d - b * c) * y = 0 := by
    calc
      (a * d - b * c) * y =
          a * (c * x + d * y) - c * (a * x + b * y) := by ring
      _ = 0 := by rw [hrow₁, hrow₂]; ring
  exact ⟨(mul_eq_zero.mp hx).resolve_left hdet,
    (mul_eq_zero.mp hy).resolve_left hdet⟩

/-- If a principal cofactor of a 3x3 matrix over an integral domain
is nonzero, every nonzero vector in its kernel has a nonzero
coordinate in that same index. The matrix need not be symmetric. -/
theorem principalCofactor_kernelVector_pivot_ne_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (H : Matrix (Fin 3) (Fin 3) R)
    (S : Fin 3 → R)
    (hker : H *ᵥ S = 0)
    (hS : S ≠ 0)
    (k : Fin 3)
    (hk : H.adjugate k k ≠ 0) :
    S k ≠ 0 := by
  classical
  intro hzero
  have hrow (i : Fin 3) :
      H i 0 * S 0 + H i 1 * S 1 + H i 2 * S 2 = 0 := by
    have hi := congrFun hker i
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.zero_apply] using hi
  fin_cases k
  · change S (0 : Fin 3) = 0 at hzero
    have hdet : H 1 1 * H 2 2 - H 1 2 * H 2 1 ≠ 0 := by
      simpa [Matrix.adjugate_fin_three] using hk
    have h1 : H 1 1 * S 1 + H 1 2 * S 2 = 0 := by
      simpa only [hzero, mul_zero, zero_add, add_zero] using hrow 1
    have h2 : H 2 1 * S 1 + H 2 2 * S 2 = 0 := by
      simpa only [hzero, mul_zero, zero_add, add_zero] using hrow 2
    obtain ⟨hS1, hS2⟩ :=
      two_by_two_kernel_zero_of_det_ne_zero
        (H 1 1) (H 1 2) (H 2 1) (H 2 2)
        (S 1) (S 2) hdet h1 h2
    apply hS
    funext i
    fin_cases i
    · exact hzero
    · exact hS1
    · exact hS2
  · change S (1 : Fin 3) = 0 at hzero
    have hdet : H 0 0 * H 2 2 - H 0 2 * H 2 0 ≠ 0 := by
      simpa [Matrix.adjugate_fin_three] using hk
    have h0 : H 0 0 * S 0 + H 0 2 * S 2 = 0 := by
      simpa only [hzero, mul_zero, zero_add, add_zero] using hrow 0
    have h2 : H 2 0 * S 0 + H 2 2 * S 2 = 0 := by
      simpa only [hzero, mul_zero, zero_add, add_zero] using hrow 2
    obtain ⟨hS0, hS2⟩ :=
      two_by_two_kernel_zero_of_det_ne_zero
        (H 0 0) (H 0 2) (H 2 0) (H 2 2)
        (S 0) (S 2) hdet h0 h2
    apply hS
    funext i
    fin_cases i
    · exact hS0
    · exact hzero
    · exact hS2
  · change S (2 : Fin 3) = 0 at hzero
    have hdet : H 0 0 * H 1 1 - H 0 1 * H 1 0 ≠ 0 := by
      simpa [Matrix.adjugate_fin_three] using hk
    have h0 : H 0 0 * S 0 + H 0 1 * S 1 = 0 := by
      simpa only [hzero, mul_zero, zero_add, add_zero] using hrow 0
    have h1 : H 1 0 * S 0 + H 1 1 * S 1 = 0 := by
      simpa only [hzero, mul_zero, zero_add, add_zero] using hrow 1
    obtain ⟨hS0, hS1⟩ :=
      two_by_two_kernel_zero_of_det_ne_zero
        (H 0 0) (H 0 1) (H 1 0) (H 1 1)
        (S 0) (S 1) hdet h0 h1
    apply hS
    funext i
    fin_cases i
    · exact hS0
    · exact hS1
    · exact hzero

end
end HC4.Polynomial.RankThreeCubic
