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
* degree two is already visible in the source-origin Hessian, hence gives an
  actual rank-two chart;
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

/-- Ordinary weight zero extracts exactly the source constant term. -/
theorem fourOrdinaryInitialForm_zero_eq_C_constantCoeff
    (R : MvPolynomial (Fin 4) K) :
    initialForm fourOrdinaryIntegerWeight 0 R =
      MvPolynomial.C (MvPolynomial.constantCoeff R) := by
  ext d
  rw [coeff_initialForm]
  by_cases hd : d = 0
  · subst d
    simp [MvPolynomial.constantCoeff_eq]
  · have hdeg : HC4.Polynomial.ordinaryDegree4 d ≠ 0 := by
      intro hz
      apply hd
      apply Finsupp.degree_eq_zero_iff.mp
      rw [finsuppDegree_eq_ordinaryDegree4]
      exact hz
    have hweight :
        Finsupp.weight fourOrdinaryIntegerWeight d ≠ (0 : ℤ) := by
      rw [fourOrdinaryIntegerWeight_eq_ordinaryDegree4]
      exact_mod_cast hdeg
    simp [hweight, hd, MvPolynomial.constantCoeff_eq]

/-- The Hessian of the exact ordinary quadratic component is the constant
source-origin Hessian of the full polynomial. -/
theorem hessian_fourOrdinaryDegreeComponent_two_eq_C_constantCoeff
    (R : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessian (fourOrdinaryDegreeComponent R 2) i j =
      MvPolynomial.C
        (MvPolynomial.constantCoeff (HC4.Polynomial.hessian R i j)) := by
  have h :=
    initialForm_fourHessianEntry_eq_componentHessian R 2 i j
  have hzero :
      initialForm fourOrdinaryIntegerWeight 0
          (HC4.Polynomial.hessian R i j) =
        MvPolynomial.C
          (MvPolynomial.constantCoeff (HC4.Polynomial.hessian R i j)) :=
    fourOrdinaryInitialForm_zero_eq_C_constantCoeff
      (HC4.Polynomial.hessian R i j)
  simpa using h.symm.trans hzero

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

/-- A nonzero principal minor on the exact ordinary quadratic component
cannot be cancelled by higher source degrees: it is exactly the constant
coefficient of the full source principal minor. -/
theorem principalMinor_source_ne_zero_of_degreeTwoComponent
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (fourOrdinaryDegreeComponent F 2) i j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor F i j ≠ 0 := by
  intro hsource
  have hconst := congrArg MvPolynomial.constantCoeff hsource
  have hscalar :
      MvPolynomial.constantCoeff (HC4.Polynomial.hessian F i i) *
            MvPolynomial.constantCoeff (HC4.Polynomial.hessian F j j) -
          MvPolynomial.constantCoeff (HC4.Polynomial.hessian F i j) *
            MvPolynomial.constantCoeff (HC4.Polynomial.hessian F j i) = 0 := by
    simpa [HC4.Polynomial.hessianPrincipalMinor] using hconst
  apply hminor
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [hessian_fourOrdinaryDegreeComponent_two_eq_C_constantCoeff,
    hessian_fourOrdinaryDegreeComponent_two_eq_C_constantCoeff,
    hessian_fourOrdinaryDegreeComponent_two_eq_C_constantCoeff,
    hessian_fourOrdinaryDegreeComponent_two_eq_C_constantCoeff]
  simpa [hscalar]

/-- A quadratic residual layer therefore immediately gives an actual rank-two
chart on the represented source. -/
noncomputable def ExactOrdinaryLayerMinorAtFirstBreak.actualRankTwoChart_of_degree_eq_two
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (L : P.ExactOrdinaryLayerMinorAtFirstBreak)
    (hdeg : L.sourceDegree = 2) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  have hlayer :
      HC4.Polynomial.hessianPrincipalMinor
        (fourOrdinaryDegreeComponent T.topKernelReesSource 2)
        L.index kernelCoordinate ≠ 0 := by
    have h := L.minor_ne_zero
    subst L.sourceDegree
    simpa [fourOrdinaryDegreeComponent, fourOrdinaryIntegerWeight,
      ordinaryTopNatWeight] using h
  have hsource :=
    principalMinor_source_ne_zero_of_degreeTwoComponent
      T.topKernelReesSource L.index kernelCoordinate hlayer
  apply actualRankTwoHessianChart_of_specialFiber_minor
    L.index_ne_kernel
  simpa [topKernelReesSource] using hsource

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

/-- **Nonlinear top-kernel first-break frontier.**

The degree-two residual is source-visible at the origin and is promoted to an
actual rank-two chart.  Hence the only remaining layer-only branch is an
exact strictly lower ordinary source layer of degree at least three. -/
theorem actualRankTwo_or_exactLowerNonlinearLayerMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactNonlinearOrdinaryLayerMinorAtFirstBreak := by
  rcases P.actualRankTwo_or_exactLowerCurvedLayerMinor with hactual | hcurved
  · exact Or.inl hactual
  · rcases hcurved with ⟨C⟩
    by_cases h2 : C.layer.sourceDegree = 2
    · exact Or.inl ⟨C.layer.actualRankTwoChart_of_degree_eq_two h2⟩
    · exact Or.inr ⟨{
        layer := C.layer
        sourceDegree_ge_three := by omega
      }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
