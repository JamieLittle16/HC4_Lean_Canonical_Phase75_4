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

/-- **Curved top-kernel first-break frontier.**

Every top-kernel linear-power branch gives either an actual rank-two chart on
the represented determinant-one source or a strictly lower exact ordinary
source layer of degree at least two carrying a nonzero principal Hessian
minor.

The remaining degree-two subcase is intentionally retained here: its correct
source lift is through the origin Hessian / quadratic component, not through a
maximal-weight argument. -/
structure ExactCurvedOrdinaryLayerMinorAtFirstBreak
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  layer : P.ExactOrdinaryLayerMinorAtFirstBreak
  sourceDegree_ge_two : 2 ≤ layer.sourceDegree

theorem actualRankTwo_or_exactLowerCurvedLayerMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactCurvedOrdinaryLayerMinorAtFirstBreak := by
  rcases P.actualRankTwo_or_exactLowerOrdinaryLayerMinor with hactual | hlayer
  · exact Or.inl hactual
  · rcases hlayer with ⟨L⟩
    exact Or.inr ⟨{
      layer := L
      sourceDegree_ge_two := L.sourceDegree_ge_two
    }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
