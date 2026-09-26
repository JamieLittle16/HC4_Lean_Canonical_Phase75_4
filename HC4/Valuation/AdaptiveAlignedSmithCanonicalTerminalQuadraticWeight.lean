import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry
import HC4.Polynomial.WeightBounds
import Mathlib.Tactic

/-!
# A19.11: the terminal quadratic branch is a conformal weight face

The symmetric Smith separator `(1,1)` has integral direction `(2,2)`.  For a
projected exponent `(b,c,d)` its derivative is

    2 * (b + c + 2*d - 2).

Hence every exponent in the surviving branch lies on or above the affine
hyperplane

    b + c + 2*d = 2,

and the canonical quadratic balanced subface is its equality face.  Reversing
signs turns this lower face into the maximal weighted face for the integral
source weight

    (0,-1,-1,-2)

at weighted degree `-2`.  The corresponding positive weight `(0,1,1,2)` is a
one-zero conformal weight of degree `2`.

This is the exact bridge needed to apply the generic maximal-Hessian-initial
lemma to the *full* quadratic Smith subface rather than to the singular
minimal-longitudinal packet.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Positive terminal quadratic source weight `(0,1,1,2)`. -/
def terminalQuadraticPositiveWeight : Fin 4 → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2

/-- Opposite weight used to make the quadratic Smith lower face maximal. -/
def terminalQuadraticNegativeWeight : Fin 4 → ℤ :=
  fun i => - terminalQuadraticPositiveWeight i

@[simp] theorem terminalQuadraticPositiveWeight_zero :
    terminalQuadraticPositiveWeight (0 : Fin 4) = 0 := rfl
@[simp] theorem terminalQuadraticPositiveWeight_one :
    terminalQuadraticPositiveWeight (1 : Fin 4) = 1 := rfl
@[simp] theorem terminalQuadraticPositiveWeight_two :
    terminalQuadraticPositiveWeight (2 : Fin 4) = 1 := rfl
@[simp] theorem terminalQuadraticPositiveWeight_three :
    terminalQuadraticPositiveWeight (3 : Fin 4) = 2 := rfl

@[simp] theorem terminalQuadraticNegativeWeight_zero :
    terminalQuadraticNegativeWeight (0 : Fin 4) = 0 := by
  simp [terminalQuadraticNegativeWeight]
@[simp] theorem terminalQuadraticNegativeWeight_one :
    terminalQuadraticNegativeWeight (1 : Fin 4) = -1 := by
  simp [terminalQuadraticNegativeWeight]
@[simp] theorem terminalQuadraticNegativeWeight_two :
    terminalQuadraticNegativeWeight (2 : Fin 4) = -1 := by
  simp [terminalQuadraticNegativeWeight]
@[simp] theorem terminalQuadraticNegativeWeight_three :
    terminalQuadraticNegativeWeight (3 : Fin 4) = -2 := by
  simp [terminalQuadraticNegativeWeight]

/-- Arithmetic identity behind the final conformal face. -/
theorem smithSeparatorDelta_one_one_eq_terminalQuadraticDegree
    (e : SmithSupportExponent) :
    smithSeparatorDelta 1 1 e =
      2 * ((e.b : ℤ) + (e.c : ℤ) + 2 * (e.d : ℤ) - 2) := by
  rcases e with ⟨b, c, d⟩
  norm_num [smithSeparatorDelta, smithExtremeSeparator,
    SmithSupportExponent.grade, smithGrade, smithGradeFirst,
    smithGradeSecond, smithGradeDot]
  ring

/-- Every general surviving Smith exponent has positive quadratic source
weight at least two. -/
theorem two_le_terminalQuadraticDegree_of_generalSurvivingShape
    (e : SmithSupportExponent)
    (hshape : HasGeneralSurvivingSmithGradeShape e) :
    2 ≤ e.b + e.c + 2 * e.d := by
  have hdelta : 0 ≤ smithSeparatorDelta 1 1 e :=
    smithSeparatorDelta_one_one_nonnegative_of_generalShape e hshape
  rw [smithSeparatorDelta_one_one_eq_terminalQuadraticDegree] at hdelta
  omega

/-- Concrete Finsupp weight formula for the negative conformal weight. -/
theorem terminalQuadraticNegativeWeight_finsupp
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight terminalQuadraticNegativeWeight d =
      -((d (1 : Fin 4) : ℤ) + (d (2 : Fin 4) : ℤ) +
        2 * (d (3 : Fin 4) : ℤ)) := by
  rw [Finsupp.weight_apply]
  simp [Finsupp.sum_fintype, Fin.sum_univ_four,
    terminalQuadraticNegativeWeight]
  ring

/-- The full terminal polynomial in the quadratic surviving branch is bounded
above by `-2` for the negative conformal weight.  Thus its quadratic Smith
face is eligible for the generic maximal-initial Hessian theorem. -/
theorem AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry.negativeWeightLE
    {RR : RepairRanking}
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    {T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR state complexity}
    (G : AdaptiveAlignedSmithCanonicalTerminalQuadraticGeometry T) :
    HC4.Polynomial.IsWeightLE
      terminalQuadraticNegativeWeight (-2) T.specialFiber := by
  intro d hd
  let e := smithSupportExponentOf (1 : Fin 4) 2 3 d
  have he :
      e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber := by
    unfold smithProjectedSupport
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hshape : HasGeneralSurvivingSmithGradeShape e :=
    G.survivingShape e he rfl
  have htwo : 2 ≤ e.b + e.c + 2 * e.d :=
    two_le_terminalQuadraticDegree_of_generalSurvivingShape e hshape
  have hcoords :
      e.b = d (1 : Fin 4) ∧
      e.c = d (2 : Fin 4) ∧
      e.d = d (3 : Fin 4) := by
    simp [e, smithSupportExponentOf]
  rw [terminalQuadraticNegativeWeight_finsupp]
  rcases hcoords with ⟨hb, hc, hw⟩
  rw [hb, hc, hw] at htwo
  omega

/-- The positive conformal weight has total weight four. -/
theorem terminalQuadraticPositiveWeight_sum :
    (∑ i : Fin 4, terminalQuadraticPositiveWeight i) = 4 := by
  simp [Fin.sum_univ_four]

/-- The negative exposure weight has total weight minus four. -/
theorem terminalQuadraticNegativeWeight_sum :
    (∑ i : Fin 4, terminalQuadraticNegativeWeight i) = -4 := by
  simp [Fin.sum_univ_four, terminalQuadraticNegativeWeight]

/-- Consequently the Hessian-determinant weight predicted from potential
weight `-2` is exactly zero in four variables. -/
theorem terminalQuadraticNegativeWeight_hessianBalance :
    (4 : ℤ) * (-2) -
        2 * ∑ i : Fin 4, terminalQuadraticNegativeWeight i = 0 := by
  rw [terminalQuadraticNegativeWeight_sum]
  norm_num

end

end HC4.Valuation
