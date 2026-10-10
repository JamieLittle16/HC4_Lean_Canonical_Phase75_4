import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisCanonicalSquareLattice
import HC4.Valuation.PrimitiveSmithEndpoint
import Mathlib.Tactic

/-!
# Canonical square: the actual strictly preclosing obstruction

For the honest marked-axis reverse-Rees family, the first actual parameter
order j satisfies j <= D < 4D - 6 = Delta.  An aligned fresh-square packet
D witnesses a nonzero coefficient at that very order j in its distinguished
source square; the canonical square weight of the monomial is exactly zero.

After fourfold ramification its coefficient at parameter order 4j is still
nonzero, while 4j < 4Delta.  Thus X^(4Delta) cannot divide the inflated
coefficient, giving an *explicit*, positive-preclosing family obstruction.

Unlike the earlier exact-closing-only theorem, the statement here requires
no impossible equality j = Delta.  It does require an honest fresh-square
packet; obtaining one in a general preclosing E3 branch remains a separate
mathematical obligation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open AdaptiveAlignedSmithRankOneClosingSourceCarrier

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}

/-- The distinguished fresh square violates coefficientwise integrality at
the true strictly preclosing first-actual parameter order.  This is the
explicit obstruction, not a classical choice of a failed coefficient. -/
noncomputable def TopKernelMarkedAxisAlignedFreshSquareData.freshSquareObstruction
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D := by
  let Delta : ℕ := 4 * T.topFace.degree - 6
  let j : ℕ := T.topKernelMarkedAxisFirstActualLayerOrder
  have hjlt : 4 * j < 4 * Delta := by
    have h := T.topKernelMarkedAxisFirstActualLayerOrder_lt_defect
    dsimp [j, Delta]
    omega
  have hsquare :
      (MvPolynomial.coeff D.squareExponent D.family).coeff j ≠ 0 := by
    simpa [j, TopKernelMarkedAxisAlignedFreshSquareData.squareExponent,
      TopKernelMarkedAxisAlignedFreshSquareData.family] using
      D.squareCoeff_closing_ne
  have hram :
      (parameterRamificationHom (K := K) 4
        (MvPolynomial.coeff D.squareExponent D.family)).coeff (4 * j) ≠ 0 := by
    rw [parameterRamificationHom_eq_expand]
    rw [Polynomial.coeff_expand_mul' (R := K) (by norm_num)]
    exact hsquare
  refine {
    exponent := D.squareExponent
    mem_family := D.squareSupport
    not_divisible := ?_
  }
  intro hdiv
  change
    Polynomial.X ^ (4 * Delta) ∣
      Polynomial.X ^
          Finsupp.weight
            (directClosingCanonicalSquareWeight Delta D.ell)
            D.squareExponent *
        parameterRamificationHom (K := K) 4
          (MvPolynomial.coeff D.squareExponent D.family) at hdiv
  rw [D.canonicalSquareWeight_squareExponent] at hdiv
  simp only [pow_zero, one_mul] at hdiv
  have hzero :=
    (Polynomial.X_pow_dvd_iff.mp hdiv) (4 * j) hjlt
  exact hram hzero

/-- Every aligned fresh-square packet explicitly forces the family-obstruction
branch of canonical-square arithmetic, without a timing equality. -/
theorem topKernelMarkedAxisCanonicalSquare_obstruction
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    Nonempty (T.TopKernelMarkedAxisCanonicalSquareFamilyObstruction D) :=
  ⟨D.freshSquareObstruction⟩

/-- This obstruction is at the positive first-actual order, not at order zero. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.freshSquareObstruction_order
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    smithFamilyCoefficientParameterOrder
        D.family
        D.freshSquareObstruction.exponent
        D.freshSquareObstruction.mem_family =
      T.topKernelMarkedAxisFirstActualLayerOrder := by
  change smithFamilyCoefficientParameterOrder
    D.family D.squareExponent D.squareSupport =
      T.topKernelMarkedAxisFirstActualLayerOrder
  exact D.squareExactOrder

/-- Explicit first-actual layer witness has positive order strictly before
the Hessian closing clock. -/
theorem TopKernelMarkedAxisAlignedFreshSquareData.freshSquareObstruction_positiveEarlier
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (D : T.TopKernelMarkedAxisAlignedFreshSquareData) :
    0 <
        smithFamilyCoefficientParameterOrder
          D.family
          D.freshSquareObstruction.exponent
          D.freshSquareObstruction.mem_family ∧
      smithFamilyCoefficientParameterOrder
          D.family
          D.freshSquareObstruction.exponent
          D.freshSquareObstruction.mem_family <
        4 * T.topFace.degree - 6 := by
  rw [D.freshSquareObstruction_order]
  exact ⟨T.topKernelMarkedAxisFirstActualLayerOrder_pos,
    T.topKernelMarkedAxisFirstActualLayerOrder_lt_defect⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
