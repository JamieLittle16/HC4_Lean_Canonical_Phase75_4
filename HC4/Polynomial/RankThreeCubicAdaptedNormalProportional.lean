import HC4.Polynomial.RankThreeCubicAdaptedNormalCofactor
import Mathlib.Tactic

/-!
# Two linear forms vanishing on an adapted plane are proportional

Let M be invertible, and let ell be a nonzero linear form with
ell(M_1)=ell(M_2)=0. Any second form gamma vanishing on
those two columns is a scalar multiple of ell.

This finite linear-algebra fact is the missing bridge between
a triple factor obtained in adapted coordinates and the original
polynomial statement p | c. It reuses the verified first row
of the adjugate frame.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators
noncomputable section

/-- A linear functional vanishing on the same two tangent
basis vectors is proportional to the pole normal. -/
theorem tangentFrame_linearFunctional_proportional
    {K : Type*} [Field K]
    (ell gamma : Fin 3 → K)
    (hell : ell ≠ 0)
    (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.det ≠ 0)
    (hM1 : (∑ i : Fin 3, ell i * M i 1) = 0)
    (hM2 : (∑ i : Fin 3, ell i * M i 2) = 0)
    (hgM1 : (∑ i : Fin 3, gamma i * M i 1) = 0)
    (hgM2 : (∑ i : Fin 3, gamma i * M i 2) = 0) :
    ∃ k : K, ∀ j : Fin 3, gamma j = k * ell j := by
  classical
  let t : K := ∑ i : Fin 3, ell i * M i 0
  let g : K := ∑ i : Fin 3, gamma i * M i 0
  have ht : t ≠ 0 :=
    tangentFrame_normal_first_ne_zero ell hell M hM hM1 hM2
  refine ⟨g / t, ?_⟩
  intro j
  have hl : t * M.adjugate 0 j = M.det * ell j :=
    tangentFrame_normal_adjugate_row ell M hM1 hM2 j
  have hg : g * M.adjugate 0 j = M.det * gamma j :=
    tangentFrame_normal_adjugate_row gamma M hgM1 hgM2 j
  have hscale : t * (M.det * gamma j) =
      g * (M.det * ell j) := by
    calc
      t * (M.det * gamma j) = t * (g * M.adjugate 0 j) := by rw [hg]
      _ = g * (t * M.adjugate 0 j) := by ring
      _ = g * (M.det * ell j) := by rw [hl]
  have hscale' : t * gamma j = g * ell j := by
    apply (mul_left_cancel₀ hM)
    calc
      M.det * (t * gamma j) = t * (M.det * gamma j) := by ring
      _ = g * (M.det * ell j) := hscale
      _ = M.det * (g * ell j) := by ring
  calc
    gamma j = (g * ell j) / t := by
      apply (eq_div_iff ht).2
      simpa only [mul_comm] using hscale'.symm
    _ = (g / t) * ell j := by ring

end
end HC4.Polynomial.RankThreeCubic
