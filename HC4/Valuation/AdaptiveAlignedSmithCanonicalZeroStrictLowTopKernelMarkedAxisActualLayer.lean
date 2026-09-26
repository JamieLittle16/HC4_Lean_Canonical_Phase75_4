import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelReverseReesCollision
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelExactClock
import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingActualLayer
import Mathlib.Tactic

/-!
# Positive actual parameter layer on the honest marked-axis top-kernel family

The zero-strict-low represented blocker itself has raw Hessian defect zero, so
its parameter family need not have any positive actual parameter layer.  The
ordinary reverse-Rees interpolation is the honest auxiliary family that
creates the missing parameter direction while preserving the marked collision.

Its exact determinant clock is `4D - 8`.  One inverse marked-axis source
inflation turns the coalescing collision `0 ~ tau e_0` into the literal
constant marked collision `0 ~ e_0`, and raises the pure Hessian defect by
exactly two.  Hence the marked-axis first-contact family has exact clock

    (4D - 8) + 2 = 4D - 6,

which is positive for every final top degree `D >= 3`.

A positive pure Hessian clock forces a genuine positive *actual* parameter
layer.  Thus the marked-axis family supplies the finite source-layer witness
needed by the next Newton supporting-lattice extraction, without pretending
that the original zero-clock blocker family itself moves in the parameter.

No terminal cocharacter, progress theorem, or JC2 input is introduced here.
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

/-- Exact pure Hessian clock of the collision-separated marked-axis family. -/
theorem topKernelMarkedAxisFirstContactFamily_hasHessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K)
      T.topKernelMarkedAxisFirstContactFamily
      (T.topKernelOrdinaryReesDefect + 2) := by
  unfold topKernelMarkedAxisFirstContactFamily
  exact
    kernelInflateHom_unit_hasHessianDefect_add_two
      (K := K) (0 : Fin 4)
      T.topKernelReverseReesFamily
      T.topKernelReverseReesFamily_hasHessianDefect

/-- The marked-axis first-contact clock is genuinely positive. -/
theorem topKernelMarkedAxisFirstContact_defect_pos :
    0 < T.topKernelOrdinaryReesDefect + 2 := by
  omega

/-- Therefore the honest marked-axis collision family contains a genuine
positive actual parameter layer. -/
theorem topKernelMarkedAxisFirstContact_hasPositiveActualParameterLayer :
    HasPositiveActualParameterLayer
      T.topKernelMarkedAxisFirstContactFamily := by
  exact
    hasPositiveActualParameterLayer_of_hessianDefect_pos
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContactFamily_hasHessianDefect
      T.topKernelMarkedAxisFirstContact_defect_pos

/-- Canonical least positive actual parameter order on the marked-axis family. -/
noncomputable def topKernelMarkedAxisFirstActualLayerOrder : ℕ :=
  firstPositiveActualParameterOrder
    T.topKernelMarkedAxisFirstContactFamily
    T.topKernelMarkedAxisFirstContact_hasPositiveActualParameterLayer

theorem topKernelMarkedAxisFirstActualLayerOrder_pos :
    0 < T.topKernelMarkedAxisFirstActualLayerOrder := by
  exact
    firstPositiveActualParameterOrder_pos
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualParameterLayer

/-- The least positive actual layer is realised by an honest supported source
monomial of the very same family that carries the constant marked collision. -/
theorem topKernelMarkedAxisFirstActualLayerOrder_realised :
    ∃ d ∈ T.topKernelMarkedAxisFirstContactFamily.support,
      (MvPolynomial.coeff d T.topKernelMarkedAxisFirstContactFamily).coeff
        T.topKernelMarkedAxisFirstActualLayerOrder ≠ 0 := by
  exact
    firstPositiveActualParameterOrder_realised
      T.topKernelMarkedAxisFirstContactFamily
      T.topKernelMarkedAxisFirstContact_hasPositiveActualParameterLayer

/-- Package the actual positive source-layer witness in the generic finite
source-layer interface already used by the closing theory. -/
theorem topKernelMarkedAxis_exists_actualPositiveLayerWitness :
    Nonempty
      (AdaptiveAlignedSmithActualPositiveLayerWitness
        T.topKernelMarkedAxisFirstContactFamily) := by
  rcases T.topKernelMarkedAxisFirstActualLayerOrder_realised with
    ⟨d, hd, hcoeff⟩
  exact ⟨{
    order := T.topKernelMarkedAxisFirstActualLayerOrder
    order_pos := T.topKernelMarkedAxisFirstActualLayerOrder_pos
    exponent := d
    sourceSupport := hd
    coefficient_ne_zero := hcoeff
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
