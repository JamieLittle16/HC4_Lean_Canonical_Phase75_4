import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelFirstBreakNonlinear
import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# Exact determinant clock for the zero-clock ordinary reverse-Rees seam

The top-kernel branch uses the honest ordinary reverse-Rees interpolation

    P(t,x) = t^D F(x/t)

between the maximal ordinary top face and the represented determinant-one
source.  Because the source Hessian determinant is exactly one, the generic
bounded reverse-Rees determinant law gives the exact clock

    det Hess(P) = t^(4D - 8).

For the final singular seam we have D >= 3, so the exponent is strictly
positive.  Thus every rank opening in the auxiliary ordinary filtration is
constrained by one literal monomial determinant clock on the same honest
source family.

This file introduces no repair state, terminal cocharacter, or JC2 input.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state)

/-- The ordinary reverse-Rees determinant exponent attached to the selected
maximal source degree. -/
def topKernelOrdinaryReesDefect : ℕ :=
  4 * T.topFace.degree - 8

/-- The sum of the four natural ordinary source weights is four. -/
theorem ordinaryTopNatWeight_sum :
    (∑ i : Fin 4, ordinaryTopNatWeight i) = 4 := by
  simp [ordinaryTopNatWeight, Fin.sum_univ_four]

/-- The generic nonnegativity side condition for the reverse-Rees determinant
law follows from the nonlinear top degree `D >= 3`. -/
theorem topKernelOrdinaryRees_clock_nonnegative :
    2 * ∑ i : Fin 4, ordinaryTopNatWeight i ≤
      4 * T.topFace.degree := by
  rw [T.ordinaryTopNatWeight_sum]
  have hD := T.topFace.degree_ge_three
  omega

/-- **Exact ordinary reverse-Rees Hessian clock.** -/
theorem topKernelReverseReesFamily_hasHessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K)
      T.topKernelReverseReesFamily
      T.topKernelOrdinaryReesDefect := by
  have h :=
    reverseWeightedReesFamily_hasHessianDefect
      ordinaryTopNatWeight
      T.topFace.degree
      T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound
      T.topKernelReesSource_hessianDeterminant_eq_one
      T.topKernelOrdinaryRees_clock_nonnegative
  simpa [topKernelReverseReesFamily, topKernelOrdinaryReesDefect,
    T.ordinaryTopNatWeight_sum] using h

/-- Expanded determinant identity for consumers that work directly with the
polynomial Hessian matrix. -/
theorem topKernelReverseReesFamily_hessianDeterminant :
    HC4.Polynomial.hessianDeterminant T.topKernelReverseReesFamily =
      MvPolynomial.C
        ((Polynomial.X : Polynomial K) ^
          T.topKernelOrdinaryReesDefect) := by
  exact T.topKernelReverseReesFamily_hasHessianDefect

/-- The ordinary reverse-Rees clock is genuinely positive at every final
singular seam. -/
theorem topKernelOrdinaryReesDefect_pos :
    0 < T.topKernelOrdinaryReesDefect := by
  unfold topKernelOrdinaryReesDefect
  have hD := T.topFace.degree_ge_three
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
