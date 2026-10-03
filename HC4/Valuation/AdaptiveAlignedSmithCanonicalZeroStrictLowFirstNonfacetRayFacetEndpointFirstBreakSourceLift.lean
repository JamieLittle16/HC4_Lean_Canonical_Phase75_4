import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointFirstBreakClosure
import HC4.Valuation.ReverseWeightedReesHessianPrincipalMinor
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Lift the whole-family endpoint first-break minor back to the represented source

The pure-axis endpoint first-break has two genuinely different outcomes.
A nonzero coefficient of a principal minor of the *whole* reverse-Rees family
lifts back to the represented source by diagonal-inflation covariance.
A principal minor formed only inside the exact breaking layer does not admit
that inference without an extra noncancellation argument, so that case is
retained explicitly.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Parameter-first transport of one ordinary Hessian principal minor, written
with the symmetric cross entry squared. -/
private theorem parameterFirstEquiv_hessianPrincipalMinor_eq_square
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor P i j) =
      parameterFirstHessian P i i * parameterFirstHessian P j j -
        parameterFirstHessian P i j * parameterFirstHessian P i j := by
  have hsym :
      HC4.Polynomial.hessian P j i =
        HC4.Polynomial.hessian P i j := by
    change
      MvPolynomial.pderiv i (MvPolynomial.pderiv j P) =
        MvPolynomial.pderiv j (MvPolynomial.pderiv i P)
    exact pderiv_comm_commRing i j P
  unfold HC4.Polynomial.hessianPrincipalMinor
  simp only [map_sub, map_mul]
  rw [hsym]
  simp [parameterFirstHessian]

private theorem hessianPrincipalMinor_eq_square
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessianPrincipalMinor F i j =
      HC4.Polynomial.hessian F i i * HC4.Polynomial.hessian F j j -
        HC4.Polynomial.hessian F i j * HC4.Polynomial.hessian F i j := by
  have hsym :
      HC4.Polynomial.hessian F j i =
        HC4.Polynomial.hessian F i j := by
    change
      MvPolynomial.pderiv i (MvPolynomial.pderiv j F) =
        MvPolynomial.pderiv j (MvPolynomial.pderiv i F)
    exact pderiv_comm_commRing i j F
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [hsym]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsRayFacetEndpointFirstBreakData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- The only endpoint first-break outcome not automatically liftable to the
represented source. -/
def LayerMinorAtFirstBreak
    (D : QsRayFacetEndpointFirstBreakData C) : Prop :=
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  let hrow := D.exposure.kernelLastBlock_kernelRow_ne_zero D.kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow
  B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j ≠ 0 ∨
    B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j ≠ 0 ∨
    B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j ≠ 0

/-- Exact source-weight-component form of the residual layer-only
first-break minor.  Unlike an actual source minor, this statement remembers
the precise interior reverse-Rees weight level where the rank-two event
occurs. -/
def ExactSourceWeightLayerMinorAtFirstBreak
    (D : QsRayFacetEndpointFirstBreakData C) : Prop :=
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  let hrow := D.exposure.kernelLastBlock_kernelRow_ne_zero D.kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow
  j ≤ D.exposure.natLevel ∧
    let L :=
      HC4.Polynomial.initialForm
        (fun i => (D.exposure.natWeight i : ℤ))
        ((D.exposure.natLevel - j : ℕ) : ℤ)
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    HC4.Polynomial.hessianPrincipalMinor L
          (kernelLastPerm D.kernelCoordinate 0) D.kernelCoordinate ≠ 0 ∨
      HC4.Polynomial.hessianPrincipalMinor L
          (kernelLastPerm D.kernelCoordinate 1) D.kernelCoordinate ≠ 0 ∨
      HC4.Polynomial.hessianPrincipalMinor L
          (kernelLastPerm D.kernelCoordinate 2) D.kernelCoordinate ≠ 0

private theorem layerMinor0_eq
    (D : QsRayFacetEndpointFirstBreakData C)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer D.exposure.reverseReesFamily j)
        (kernelLastPerm D.kernelCoordinate 0)
        (kernelLastPerm D.kernelCoordinate 3) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff]
  rw [hessianPrincipalMinor_eq_square]

private theorem layerMinor1_eq
    (D : QsRayFacetEndpointFirstBreakData C)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer D.exposure.reverseReesFamily j)
        (kernelLastPerm D.kernelCoordinate 1)
        (kernelLastPerm D.kernelCoordinate 3) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff]
  rw [hessianPrincipalMinor_eq_square]

private theorem layerMinor2_eq
    (D : QsRayFacetEndpointFirstBreakData C)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer D.exposure.reverseReesFamily j)
        (kernelLastPerm D.kernelCoordinate 2)
        (kernelLastPerm D.kernelCoordinate 3) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff]
  rw [hessianPrincipalMinor_eq_square]

/-- A layer-only first-break event is exactly rank-two Hessian geometry on one
honest source weight component.  The component need not be maximal, so this
theorem intentionally stops short of claiming a nonzero minor on the whole
represented source. -/
theorem layerMinorAtFirstBreak_exactSourceWeightComponent
    (D : QsRayFacetEndpointFirstBreakData C)
    (h : D.LayerMinorAtFirstBreak) :
    D.ExactSourceWeightLayerMinorAtFirstBreak := by
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  let hrow := D.exposure.kernelLastBlock_kernelRow_ne_zero D.kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow
  let L := familyParameterLayer D.exposure.reverseReesFamily j
  have hminor :
      HC4.Polynomial.hessianPrincipalMinor L
            (kernelLastPerm D.kernelCoordinate 0)
            (kernelLastPerm D.kernelCoordinate 3) ≠ 0 ∨
        HC4.Polynomial.hessianPrincipalMinor L
            (kernelLastPerm D.kernelCoordinate 1)
            (kernelLastPerm D.kernelCoordinate 3) ≠ 0 ∨
        HC4.Polynomial.hessianPrincipalMinor L
            (kernelLastPerm D.kernelCoordinate 2)
            (kernelLastPerm D.kernelCoordinate 3) ≠ 0 := by
    change
      B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j ≠ 0 ∨
        B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j ≠ 0 ∨
        B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j ≠ 0 at h
    rcases h with h0 | h1 | h2
    · left
      rw [← D.layerMinor0_eq j]
      exact h0
    · right
      left
      rw [← D.layerMinor1_eq j]
      exact h1
    · right
      right
      rw [← D.layerMinor2_eq j]
      exact h2
  have hLne : L ≠ 0 := by
    intro hzero
    rcases hminor with h0 | h1 | h2
    · apply h0
      rw [hzero]
      simp [HC4.Polynomial.hessianPrincipalMinor,
        HC4.Polynomial.hessian_apply]
    · apply h1
      rw [hzero]
      simp [HC4.Polynomial.hessianPrincipalMinor,
        HC4.Polynomial.hessian_apply]
    · apply h2
      rw [hzero]
      simp [HC4.Polynomial.hessianPrincipalMinor,
        HC4.Polynomial.hessian_apply]
  have hexact :=
    reverseWeightedReesFamily_parameterLayer_eq_initialForm_of_ne_zero
      D.exposure.natWeight D.exposure.natLevel j
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      D.exposure.hasReverseWeightBound
      (by
        simpa [L,
          QsRayFacetEndpointSourceExposure.reverseReesFamily] using hLne)
  rcases hexact with ⟨hj, hexact⟩
  have hexact' :
      L =
        HC4.Polynomial.initialForm
          (fun i => (D.exposure.natWeight i : ℤ))
          ((D.exposure.natLevel - j : ℕ) : ℤ)
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
    simpa [L, QsRayFacetEndpointSourceExposure.reverseReesFamily] using hexact
  unfold ExactSourceWeightLayerMinorAtFirstBreak
  dsimp only
  refine ⟨hj, ?_⟩
  rw [← hexact']
  simpa only [kernelLastPerm_last] using hminor

private theorem familyMinor0_eq
    (D : QsRayFacetEndpointFirstBreakData C) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.a * B.z - B.q * B.q =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 0)
          (kernelLastPerm D.kernelCoordinate 3)) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square
      D.exposure.reverseReesFamily
      (kernelLastPerm D.kernelCoordinate 0)
      (kernelLastPerm D.kernelCoordinate 3)).symm

private theorem familyMinor1_eq
    (D : QsRayFacetEndpointFirstBreakData C) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.d * B.z - B.s * B.s =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 1)
          (kernelLastPerm D.kernelCoordinate 3)) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square
      D.exposure.reverseReesFamily
      (kernelLastPerm D.kernelCoordinate 1)
      (kernelLastPerm D.kernelCoordinate 3)).symm

private theorem familyMinor2_eq
    (D : QsRayFacetEndpointFirstBreakData C) :
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.x * B.z - B.y * B.y =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 2)
          (kernelLastPerm D.kernelCoordinate 3)) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square
      D.exposure.reverseReesFamily
      (kernelLastPerm D.kernelCoordinate 2)
      (kernelLastPerm D.kernelCoordinate 3)).symm

private theorem sourceMinor0_of_familyMinor
    (D : QsRayFacetEndpointFirstBreakData C)
    {j : ℕ}
    (h :
      ((kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).a *
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).z -
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).q *
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).q).coeff j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (kernelLastPerm D.kernelCoordinate 0) D.kernelCoordinate ≠ 0 := by
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  have hpoly : B.a * B.z - B.q * B.q ≠ 0 := by
    intro hz
    apply h
    have hc := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff j) hz
    simpa [B] using hc
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 0)
          (kernelLastPerm D.kernelCoordinate 3)) ≠ 0 := by
    rw [← D.familyMinor0_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 0)
          (kernelLastPerm D.kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  have hlift :=
    reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
      D.exposure.natWeight D.exposure.natLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      D.exposure.hasReverseWeightBound
      (kernelLastPerm D.kernelCoordinate 0)
      (kernelLastPerm D.kernelCoordinate 3)
      (by
        simpa [QsRayFacetEndpointSourceExposure.reverseReesFamily] using hfamily)
  simpa only [kernelLastPerm_last] using hlift

private theorem sourceMinor1_of_familyMinor
    (D : QsRayFacetEndpointFirstBreakData C)
    {j : ℕ}
    (h :
      ((kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).d *
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).z -
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).s *
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).s).coeff j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (kernelLastPerm D.kernelCoordinate 1) D.kernelCoordinate ≠ 0 := by
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  have hpoly : B.d * B.z - B.s * B.s ≠ 0 := by
    intro hz
    apply h
    have hc := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff j) hz
    simpa [B] using hc
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 1)
          (kernelLastPerm D.kernelCoordinate 3)) ≠ 0 := by
    rw [← D.familyMinor1_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 1)
          (kernelLastPerm D.kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  have hlift :=
    reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
      D.exposure.natWeight D.exposure.natLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      D.exposure.hasReverseWeightBound
      (kernelLastPerm D.kernelCoordinate 1)
      (kernelLastPerm D.kernelCoordinate 3)
      (by
        simpa [QsRayFacetEndpointSourceExposure.reverseReesFamily] using hfamily)
  simpa only [kernelLastPerm_last] using hlift

private theorem sourceMinor2_of_familyMinor
    (D : QsRayFacetEndpointFirstBreakData C)
    {j : ℕ}
    (h :
      ((kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).x *
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).z -
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).y *
        (kernelLastFamilyHessianFourBlock
          D.exposure.reverseReesFamily D.kernelCoordinate).y).coeff j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (kernelLastPerm D.kernelCoordinate 2) D.kernelCoordinate ≠ 0 := by
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  have hpoly : B.x * B.z - B.y * B.y ≠ 0 := by
    intro hz
    apply h
    have hc := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff j) hz
    simpa [B] using hc
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 2)
          (kernelLastPerm D.kernelCoordinate 3)) ≠ 0 := by
    rw [← D.familyMinor2_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily
          (kernelLastPerm D.kernelCoordinate 2)
          (kernelLastPerm D.kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  have hlift :=
    reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
      D.exposure.natWeight D.exposure.natLevel
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      D.exposure.hasReverseWeightBound
      (kernelLastPerm D.kernelCoordinate 2)
      (kernelLastPerm D.kernelCoordinate 3)
      (by
        simpa [QsRayFacetEndpointSourceExposure.reverseReesFamily] using hfamily)
  simpa only [kernelLastPerm_last] using hlift

private noncomputable def actualRankTwoChart0
    (D : QsRayFacetEndpointFirstBreakData C)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
          (kernelLastPerm D.kernelCoordinate 0) D.kernelCoordinate ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho := kernelLastPerm D.kernelCoordinate
  let sigma : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
  let pi : Equiv.Perm (Fin 4) := sigma.trans rho
  have hs0 : sigma 0 = (0 : Fin 4) := by native_decide
  have hs1 : sigma 1 = (3 : Fin 4) := by native_decide
  refine {
    permutation := pi
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  change
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (rho (sigma 0)) (rho (sigma 1)) ≠ 0
  rw [hs0, hs1]
  simpa [rho, kernelLastPerm_last] using hminor

private noncomputable def actualRankTwoChart1
    (D : QsRayFacetEndpointFirstBreakData C)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
          (kernelLastPerm D.kernelCoordinate 1) D.kernelCoordinate ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho := kernelLastPerm D.kernelCoordinate
  let sigma : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)
  let pi : Equiv.Perm (Fin 4) := sigma.trans rho
  have hs0 : sigma 0 = (1 : Fin 4) := by native_decide
  have hs1 : sigma 1 = (3 : Fin 4) := by native_decide
  refine {
    permutation := pi
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  change
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (rho (sigma 0)) (rho (sigma 1)) ≠ 0
  rw [hs0, hs1]
  simpa [rho, kernelLastPerm_last] using hminor

private noncomputable def actualRankTwoChart2
    (D : QsRayFacetEndpointFirstBreakData C)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
          (kernelLastPerm D.kernelCoordinate 2) D.kernelCoordinate ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho := kernelLastPerm D.kernelCoordinate
  let sigma : Equiv.Perm (Fin 4) :=
    (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)
  let pi : Equiv.Perm (Fin 4) := sigma.trans rho
  have hs0 : sigma 0 = (2 : Fin 4) := by native_decide
  have hs1 : sigma 1 = (3 : Fin 4) := by native_decide
  refine {
    permutation := pi
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  change
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (rho (sigma 0)) (rho (sigma 1)) ≠ 0
  rw [hs0, hs1]
  simpa [rho, kernelLastPerm_last] using hminor

/-- **Endpoint first-break refinement.**  A whole-family first-break minor
already gives an actual rank-two chart on the represented source.  The only
remaining auxiliary branch is a principal minor formed entirely inside the
exact breaking parameter layer. -/
theorem actualRankTwo_or_layerMinor
    (D : QsRayFacetEndpointFirstBreakData C) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      D.LayerMinorAtFirstBreak := by
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  let hrow := D.exposure.kernelLastBlock_kernelRow_ne_zero D.kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow
  have hout := D.firstBreakRankTwoOutcome
  change RankOneSpecialFiberFirstBreakOutcome B j at hout
  cases hout with
  | familyMinor h =>
      rcases h with h0 | h1 | h2
      · left
        exact ⟨D.actualRankTwoChart0
          (D.sourceMinor0_of_familyMinor (j := j) h0)⟩
      · left
        exact ⟨D.actualRankTwoChart1
          (D.sourceMinor1_of_familyMinor (j := j) h1)⟩
      · left
        exact ⟨D.actualRankTwoChart2
          (D.sourceMinor2_of_familyMinor (j := j) h2)⟩
  | layerMinor h =>
      right
      exact h



/-- **Source-honest endpoint first-break frontier.**  The residual auxiliary
layer case is immediately rewritten as an exact weighted component of the
represented determinant-one source.  Thus callers above this file never need
to reason about an opaque Rees-layer minor: they see either an actual source
rank-two chart or a concrete source weight component carrying a nonzero
principal Hessian minor. -/
theorem actualRankTwo_or_exactSourceWeightLayerMinor
    (D : QsRayFacetEndpointFirstBreakData C) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      D.ExactSourceWeightLayerMinorAtFirstBreak := by
  rcases D.actualRankTwo_or_layerMinor with hactual | hlayer
  · exact Or.inl hactual
  · exact Or.inr (D.layerMinorAtFirstBreak_exactSourceWeightComponent hlayer)

end QsRayFacetEndpointFirstBreakData
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
