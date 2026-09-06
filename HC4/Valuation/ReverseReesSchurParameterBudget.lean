import HC4.Valuation.ReverseReesHessianParameterBudget
import HC4.Valuation.PermutedFamilyHessianFourBlock
import HC4.Newton.RankOneSchurSeriesAlignment
import Mathlib.Tactic

/-!
# Cubic Schur coefficient budgets

Consumes: exact Hessian-entry parameter budgets.
Produces: sharp budgets for all three cleared Schur entries and closing-order
vanishing when both complementary weights are below half the source level.
Next consumer: the actual ray clock. No global progress is asserted.
-/
namespace HC4.Valuation
noncomputable section
open HC4.Newton

structure FourBlockParameterBudget {A : Type*} [CommRing A]
    (H : GeneralFourBlock (Polynomial A)) (L wa wb wc wd : ℕ) : Prop where
  a : HasParameterBudget H.a L (wa + wa)
  b : HasParameterBudget H.b L (wa + wb)
  d : HasParameterBudget H.d L (wb + wb)
  p : HasParameterBudget H.p L (wa + wc)
  q : HasParameterBudget H.q L (wa + wd)
  r : HasParameterBudget H.r L (wb + wc)
  s : HasParameterBudget H.s L (wb + wd)
  x : HasParameterBudget H.x L (wc + wc)
  y : HasParameterBudget H.y L (wc + wd)
  z : HasParameterBudget H.z L (wd + wd)

namespace FourBlockParameterBudget
variable {A : Type*} [CommRing A]
variable {H : GeneralFourBlock (Polynomial A)} {L wa wb wc wd : ℕ}

theorem activeDet (B : FourBlockParameterBudget H L wa wb wc wd) :
    HasParameterBudget H.activeDet (2 * L) (2 * wa + 2 * wb) := by
  unfold GeneralFourBlock.activeDet
  apply HasParameterBudget.sub
  · convert B.a.mul B.d using 1 <;> omega
  · convert B.b.mul B.b using 1 <;> omega

theorem schurA (B : FourBlockParameterBudget H L wa wb wc wd) :
    HasParameterBudget H.schurA (3 * L) (2 * wa + 2 * wb + 2 * wc) := by
  have ht : HasParameterBudget (H.activeDet * H.x) (3 * L) (2 * wa + 2 * wb + 2 * wc) := by
    convert B.activeDet.mul B.x using 1 <;> omega
  have h0 : HasParameterBudget (H.d * H.p * H.p) (3 * L) (2 * wa + 2 * wb + 2 * wc) := by
    convert (B.d.mul B.p).mul B.p using 1 <;> omega
  have h1 : HasParameterBudget (2 * H.b * H.p * H.r) (3 * L) (2 * wa + 2 * wb + 2 * wc) := by
    convert (B.b.twice.mul B.p).mul B.r using 1 <;> omega
  have h2 : HasParameterBudget (H.a * H.r * H.r) (3 * L) (2 * wa + 2 * wb + 2 * wc) := by
    convert (B.a.mul B.r).mul B.r using 1 <;> omega
  exact ht.sub ((h0.sub h1).add h2)

theorem schurC (B : FourBlockParameterBudget H L wa wb wc wd) :
    HasParameterBudget H.schurC (3 * L) (2 * wa + 2 * wb + 2 * wd) := by
  have ht : HasParameterBudget (H.activeDet * H.z) (3 * L) (2 * wa + 2 * wb + 2 * wd) := by
    convert B.activeDet.mul B.z using 1 <;> omega
  have h0 : HasParameterBudget (H.d * H.q * H.q) (3 * L) (2 * wa + 2 * wb + 2 * wd) := by
    convert (B.d.mul B.q).mul B.q using 1 <;> omega
  have h1 : HasParameterBudget (2 * H.b * H.q * H.s) (3 * L) (2 * wa + 2 * wb + 2 * wd) := by
    convert (B.b.twice.mul B.q).mul B.s using 1 <;> omega
  have h2 : HasParameterBudget (H.a * H.s * H.s) (3 * L) (2 * wa + 2 * wb + 2 * wd) := by
    convert (B.a.mul B.s).mul B.s using 1 <;> omega
  exact ht.sub ((h0.sub h1).add h2)

theorem schurB (B : FourBlockParameterBudget H L wa wb wc wd) :
    HasParameterBudget H.schurB (3 * L) (2 * wa + 2 * wb + wc + wd) := by
  have ht : HasParameterBudget (H.activeDet * H.y) (3 * L) (2 * wa + 2 * wb + wc + wd) := by
    convert B.activeDet.mul B.y using 1 <;> omega
  have h0 : HasParameterBudget (H.d * H.p * H.q) (3 * L) (2 * wa + 2 * wb + wc + wd) := by
    convert (B.d.mul B.p).mul B.q using 1 <;> omega
  have h1 : HasParameterBudget (H.b * H.p * H.s) (3 * L) (2 * wa + 2 * wb + wc + wd) := by
    convert (B.b.mul B.p).mul B.s using 1 <;> omega
  have h2 : HasParameterBudget (H.b * H.q * H.r) (3 * L) (2 * wa + 2 * wb + wc + wd) := by
    convert (B.b.mul B.q).mul B.r using 1 <;> omega
  have h3 : HasParameterBudget (H.a * H.r * H.s) (3 * L) (2 * wa + 2 * wb + wc + wd) := by
    convert (B.a.mul B.r).mul B.s using 1 <;> omega
  have heq : H.schurB = H.activeDet * H.y -
      (H.d * H.p * H.q - (H.b * H.p * H.s + H.b * H.q * H.r) + H.a * H.r * H.s) := by
    unfold GeneralFourBlock.schurB
    ring
  rw [heq]
  exact ht.sub ((h0.sub (h1.add h2)).add h3)

/-- No raw Schur coefficient occurs at or after the determinant clock. -/
theorem schur_coeffs_eq_zero_of_clock_le
    (B : FourBlockParameterBudget H L wa wb wc wd)
    (hmargin : 2 * L < 4 * L - 2 * (wa + wb + wc + wd))
    (hc : 2 * wc < L) (hd : 2 * wd < L)
    (n : ℕ) (hn : 4 * L - 2 * (wa + wb + wc + wd) ≤ n) :
    H.schurA.coeff n = 0 ∧ H.schurB.coeff n = 0 ∧ H.schurC.coeff n = 0 := by
  exact ⟨B.schurA n (by omega), B.schurB n (by omega), B.schurC n (by omega)⟩

/-- Polynomial source coefficients in constant alignment preserve the bound. -/
theorem alignLeft_transverse_coeffs_eq_zero_of_clock_le
    (B : FourBlockParameterBudget H L wa wb wc wd)
    (hmargin : 2 * L < 4 * L - 2 * (wa + wb + wc + wd))
    (hc : 2 * wc < L) (hd : 2 * wd < L)
    (hleft : H.polynomialSchurSeries.LeftPivot)
    (n : ℕ) (hn : 4 * L - 2 * (wa + wb + wc + wd) ≤ n) :
    (H.polynomialSchurSeries.alignLeft hleft).offDiag.coeff n = 0 ∧
    (H.polynomialSchurSeries.alignLeft hleft).kernel.coeff n = 0 := by
  rcases B.schur_coeffs_eq_zero_of_clock_le hmargin hc hd n hn with ⟨ha, hb, hz⟩
  simp [BinarySchurPolynomialSeries.alignLeft, GeneralFourBlock.polynomialSchurSeries,
    Polynomial.coeff_C_mul, ← Polynomial.C_pow, ha, hb, hz]

end FourBlockParameterBudget

/-- The budgets are proved for the actual coordinate-permuted Rees Hessian. -/
theorem reverseWeightedRees_fourBlockParameterBudget
    {K : Type*} [Field K] [CharZero K]
    (w : Fin 4 → ℕ) (L : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w L F) (rho : Equiv.Perm (Fin 4)) :
    FourBlockParameterBudget
      (permutedFamilyHessianFourBlock rho (reverseWeightedReesFamily w L F h))
      L (w (rho 0)) (w (rho 1)) (w (rho 2)) (w (rho 3)) := by
  constructor <;> exact reverseWeightedRees_parameterFirstHessian_budget w L F h _ _
end
end HC4.Valuation
