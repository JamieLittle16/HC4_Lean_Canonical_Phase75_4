import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# Exact parameter budgets with derivative weight retained

Consumes: a bounded reverse Rees source.
Produces: coefficient vanishing when parameter order plus Hessian derivative
weight exceeds the source level, and elementary product/sum closure.
Next consumer: cubic Schur entry bounds. No terminal progress is asserted.
-/
namespace HC4.Valuation
noncomputable section

/-- A coefficient can occur only if its parameter order plus the retained
weight loss is at most the level. This avoids truncated degree subtraction. -/
def HasParameterBudget {A : Type*} [Semiring A]
    (f : Polynomial A) (level loss : ℕ) : Prop :=
  ∀ n, level < n + loss → f.coeff n = 0

namespace HasParameterBudget
variable {A : Type*} [CommRing A]
variable {f g : Polynomial A} {L M a b : ℕ}

theorem add (hf : HasParameterBudget f L a) (hg : HasParameterBudget g L a) :
    HasParameterBudget (f + g) L a := by
  intro n hn
  simp only [Polynomial.coeff_add, hf n hn, hg n hn, add_zero]

theorem sub (hf : HasParameterBudget f L a) (hg : HasParameterBudget g L a) :
    HasParameterBudget (f - g) L a := by
  intro n hn
  simp only [Polynomial.coeff_sub, hf n hn, hg n hn, sub_self]

theorem mul (hf : HasParameterBudget f L a) (hg : HasParameterBudget g M b) :
    HasParameterBudget (f * g) (L + M) (a + b) := by
  intro n hn
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hs := Finset.mem_antidiagonal.mp hij
  by_cases hi : L < ij.1 + a
  · rw [hf ij.1 hi, zero_mul]
  · have hj : M < ij.2 + b := by omega
    rw [hg ij.2 hj, mul_zero]

theorem twice (hf : HasParameterBudget f L a) :
    HasParameterBudget (2 * f) L a := by
  rw [two_mul]
  exact hf.add hf
end HasParameterBudget

open HC4.Newton HC4.Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- Sharp coefficient bound for each entry of the genuine Rees Hessian. -/
theorem reverseWeightedRees_parameterFirstHessian_budget
    (w : Fin 4 → ℕ) (L : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w L F) (i j : Fin 4) :
    HasParameterBudget
      (parameterFirstHessian (reverseWeightedReesFamily w L F h) i j)
      L (w i + w j) := by
  intro n hn
  rw [parameterFirstHessian_coeff]
  apply MvPolynomial.ext
  intro d
  change MvPolynomial.coeff d
    (MvPolynomial.pderiv j (MvPolynomial.pderiv i
      (familyParameterLayer (reverseWeightedReesFamily w L F h) n))) = _
  rw [coeff_pderiv_backport, coeff_pderiv_backport, MvPolynomial.coeff_zero,
    reverseWeightedReesFamily_parameterLayer_coeff]
  split_ifs with hd
  · have hb := h _ hd.1
    have hw : Finsupp.weight w (d + Finsupp.single j 1 + Finsupp.single i 1) =
        Finsupp.weight w d + w j + w i := by
      simp only [map_add, Finsupp.weight_single, one_nsmul]
    rw [hw] at hb
    have heq := hd.2
    rw [hw] at heq
    omega
  · simp
end
end HC4.Valuation
