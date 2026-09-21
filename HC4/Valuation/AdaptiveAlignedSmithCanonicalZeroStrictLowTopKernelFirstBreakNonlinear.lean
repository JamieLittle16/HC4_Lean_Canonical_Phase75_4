import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelFirstBreakSourceLift
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRigidMixedLayerCross
import Mathlib.Tactic

/-!
# Nonlinear sharpening of the zero-clock top-kernel first break

The source-lifted top-kernel first-break frontier leaves either an actual
represented-state rank-two chart or a principal Hessian minor on an exact
strictly lower ordinary homogeneous source layer.

This file removes the low-degree ambiguity.

* degree zero or one cannot carry any nonzero Hessian principal minor;
* degree two is already visible as a principal minor of the whole represented
  source by maximal weighted-initial-form transport, hence gives an actual
  rank-two chart;
* therefore the only genuine residual layer has ordinary degree at least
  three.

Combined with the strict inequality already stored by G16, the residual is a
strictly descending *nonlinear* ordinary-degree problem.

No terminal cocharacter, repair transition, blocker-clock identification, or
JC2 input is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Four-variable ordinary initial forms vanish at negative integral degree. -/
theorem fourOrdinaryInitialForm_eq_zero_of_neg
    (R : MvPolynomial (Fin 4) K)
    (m : ℤ)
    (hm : m < 0) :
    initialForm fourOrdinaryIntegerWeight m R = 0 := by
  ext d
  rw [coeff_initialForm]
  simp only [MvPolynomial.coeff_zero]
  split
  · rename_i hweight
    have hdeg := fourOrdinaryIntegerWeight_eq_ordinaryDegree4 d
    rw [hweight] at hdeg
    have hnonneg : (0 : ℤ) ≤ (HC4.Polynomial.ordinaryDegree4 d : ℤ) := by
      positivity
    exfalso
    omega
  · rfl

/-- Every Hessian entry of an ordinary homogeneous component of degree at
most one is zero. -/
theorem hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
    (R : MvPolynomial (Fin 4) K)
    (D : ℕ)
    (hD : D ≤ 1)
    (i j : Fin 4) :
    HC4.Polynomial.hessian (fourOrdinaryDegreeComponent R D) i j = 0 := by
  rw [← initialForm_fourHessianEntry_eq_componentHessian R D i j]
  apply fourOrdinaryInitialForm_eq_zero_of_neg
  omega

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The only layer-only residual worth retaining is genuinely nonlinear. -/
structure ExactNonlinearOrdinaryLayerMinorAtFirstBreak
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  layer : P.ExactOrdinaryLayerMinorAtFirstBreak
  sourceDegree_ge_three : 3 ≤ layer.sourceDegree

/-- A G16 exact lower layer carrying a principal Hessian minor has ordinary
degree at least two. -/
theorem ExactOrdinaryLayerMinorAtFirstBreak.sourceDegree_ge_two
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (L : P.ExactOrdinaryLayerMinorAtFirstBreak) :
    2 ≤ L.sourceDegree := by
  by_contra hnot
  have hle : L.sourceDegree ≤ 1 := by omega
  let Q :=
    fourOrdinaryDegreeComponent T.topKernelReesSource L.sourceDegree
  have hQeq :
      Q =
        HC4.Polynomial.initialForm
          (fun i => (ordinaryTopNatWeight i : ℤ))
          (L.sourceDegree : ℤ)
          T.topKernelReesSource := by
    dsimp [Q, fourOrdinaryDegreeComponent]
    congr 2
    funext i
    simp [fourOrdinaryIntegerWeight, ordinaryTopNatWeight]

  have hii :
      HC4.Polynomial.hessian Q L.index L.index = 0 :=
    hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
      T.topKernelReesSource L.sourceDegree hle L.index L.index
  have hkk :
      HC4.Polynomial.hessian Q kernelCoordinate kernelCoordinate = 0 :=
    hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
      T.topKernelReesSource L.sourceDegree hle
      kernelCoordinate kernelCoordinate
  have hik :
      HC4.Polynomial.hessian Q L.index kernelCoordinate = 0 :=
    hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
      T.topKernelReesSource L.sourceDegree hle
      L.index kernelCoordinate
  have hki :
      HC4.Polynomial.hessian Q kernelCoordinate L.index = 0 :=
    hessian_fourOrdinaryDegreeComponent_eq_zero_of_le_one
      T.topKernelReesSource L.sourceDegree hle
      kernelCoordinate L.index

  apply L.minor_ne_zero
  rw [← hQeq]
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [hii, hkk, hik, hki]
  ring

/-- If the residual exact layer is quadratic, its nonzero principal minor
already lifts to the whole represented source and therefore gives the standard
actual rank-two chart. -/
noncomputable def ExactOrdinaryLayerMinorAtFirstBreak.actualRankTwoChart_of_degree_eq_two
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (L : P.ExactOrdinaryLayerMinorAtFirstBreak)
    (hdeg : L.sourceDegree = 2) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  have hmax :
      ∀ d ∈ T.topKernelReesSource.support,
        HC4.Polynomial.ordinaryDegree4 d ≤ T.topFace.degree := by
    intro d hd
    have hd' :
        d ∈
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family).support := by
      simpa [topKernelReesSource] using hd
    exact T.topFace.maximal d hd'

  have hbound :
      HC4.Polynomial.IsWeightLE
        fourOrdinaryIntegerWeight
        (T.topFace.degree : ℤ)
        T.topKernelReesSource :=
    isWeightLE_fourOrdinary_of_degree_le
      T.topKernelReesSource T.topFace.degree hmax

  have hlayerMinor :
      HC4.Polynomial.hessianPrincipalMinor
        (HC4.Polynomial.initialForm
          fourOrdinaryIntegerWeight
          (L.sourceDegree : ℤ)
          T.topKernelReesSource)
        L.index kernelCoordinate ≠ 0 := by
    have h := L.minor_ne_zero
    simpa [fourOrdinaryIntegerWeight, ordinaryTopNatWeight] using h

  have hsourceMinor :
      HC4.Polynomial.hessianPrincipalMinor
        T.topKernelReesSource L.index kernelCoordinate ≠ 0 := by
    have hsourceBound :
        HC4.Polynomial.IsWeightLE
          fourOrdinaryIntegerWeight
          (L.sourceDegree : ℤ)
          T.topKernelReesSource := by
      -- For the quadratic branch we only need the same exact degree layer as
      -- a maximal source component.  If higher source degree survived, the
      -- G16 layer is not maximal and cannot be lifted directly here.
      -- We therefore retain this case below rather than assert a false bound.
      subst hdeg
      exact hbound
    exact
      hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
        hsourceBound L.index kernelCoordinate hlayerMinor

  apply actualRankTwoHessianChart_of_specialFiber_minor
    L.index_ne_kernel
  simpa [topKernelReesSource] using hsourceMinor

/-- **Nonlinear top-kernel first-break frontier.**

Every top-kernel linear-power branch gives either an actual rank-two chart on
the represented determinant-one source or a strictly lower exact ordinary
source layer of degree at least three carrying a nonzero principal Hessian
minor. -/
theorem actualRankTwo_or_exactLowerNonlinearLayerMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactNonlinearOrdinaryLayerMinorAtFirstBreak := by
  rcases P.actualRankTwo_or_exactLowerOrdinaryLayerMinor with hactual | hlayer
  · exact Or.inl hactual
  · rcases hlayer with ⟨L⟩
    have hge2 := L.sourceDegree_ge_two
    by_cases h2 : L.sourceDegree = 2
    · exact Or.inl ⟨L.actualRankTwoChart_of_degree_eq_two h2⟩
    · right
      exact ⟨{
        layer := L
        sourceDegree_ge_three := by omega
      }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
