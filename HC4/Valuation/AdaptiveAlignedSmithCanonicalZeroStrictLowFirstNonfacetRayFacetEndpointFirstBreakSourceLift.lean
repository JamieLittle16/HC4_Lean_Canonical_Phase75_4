import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointFirstBreakClosure
import HC4.Valuation.ReverseWeightedReesHessianPrincipalMinor
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Lift the whole-family endpoint first-break minor back to the represented source

The pure-axis lower-ray endpoint produces an honest bounded reverse-Rees
first-break packet.  Its generic rank-two outcome has two logically distinct
constructors:

* `familyMinor`: a coefficient of a principal minor of the whole reverse-Rees
  Hessian is nonzero;
* `layerMinor`: the principal minor formed from one exact parameter layer is
  nonzero.

Only the first constructor lifts directly to the represented source.  This
file performs that lift through the exact parameter-first equivalence and the
diagonal-inflation theorem in `ReverseWeightedReesHessianPrincipalMinor`.
The layer-only constructor is retained explicitly; no cross-layer
noncancellation is assumed.
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
  unfold HC4.Polynomial.hessianPrincipalMinor parameterFirstHessian
  simp only [Matrix.map_apply, map_sub, map_mul]
  rw [hsym]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsRayFacetEndpointFirstBreakData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- The only endpoint first-break outcome not automatically liftable to the
represented source: a nonzero principal minor formed inside the exact breaking
parameter layer. -/
def LayerMinorAtFirstBreak
    (D : QsRayFacetEndpointFirstBreakData C) : Prop :=
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  let hrow := D.exposure.kernelLastBlock_kernelRow_ne_zero D.kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow
  B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j ≠ 0 ∨
    B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j ≠ 0 ∨
    B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j ≠ 0

private theorem familyMinor0_eq
    (D : QsRayFacetEndpointFirstBreakData C) :
    let rho := kernelLastPerm D.kernelCoordinate
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.a * B.z - B.q * B.q =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 0) (rho 3)) := by
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
    let rho := kernelLastPerm D.kernelCoordinate
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.d * B.z - B.s * B.s =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 1) (rho 3)) := by
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
    let rho := kernelLastPerm D.kernelCoordinate
    let B := kernelLastFamilyHessianFourBlock
      D.exposure.reverseReesFamily D.kernelCoordinate
    B.x * B.z - B.y * B.y =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 2) (rho 3)) := by
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
      let B := kernelLastFamilyHessianFourBlock
        D.exposure.reverseReesFamily D.kernelCoordinate
      (B.a * B.z - B.q * B.q).coeff j ≠ 0) :
    let rho := kernelLastPerm D.kernelCoordinate
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (rho 0) (rho 3) ≠ 0 := by
  let rho := kernelLastPerm D.kernelCoordinate
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  have hpoly : B.a * B.z - B.q * B.q ≠ 0 := by
    intro hz
    apply h
    dsimp only [B]
    rw [hz]
    simp
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 0) (rho 3)) ≠ 0 := by
    rw [← D.familyMinor0_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 0) (rho 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  dsimp only [rho]
  apply reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    D.exposure.natWeight D.exposure.natLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    D.exposure.hasReverseWeightBound
    (kernelLastPerm D.kernelCoordinate 0)
    (kernelLastPerm D.kernelCoordinate 3)
  simpa [QsRayFacetEndpointSourceExposure.reverseReesFamily] using hfamily

private theorem sourceMinor1_of_familyMinor
    (D : QsRayFacetEndpointFirstBreakData C)
    {j : ℕ}
    (h :
      let B := kernelLastFamilyHessianFourBlock
        D.exposure.reverseReesFamily D.kernelCoordinate
      (B.d * B.z - B.s * B.s).coeff j ≠ 0) :
    let rho := kernelLastPerm D.kernelCoordinate
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (rho 1) (rho 3) ≠ 0 := by
  let rho := kernelLastPerm D.kernelCoordinate
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  have hpoly : B.d * B.z - B.s * B.s ≠ 0 := by
    intro hz
    apply h
    dsimp only [B]
    rw [hz]
    simp
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 1) (rho 3)) ≠ 0 := by
    rw [← D.familyMinor1_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 1) (rho 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  dsimp only [rho]
  apply reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    D.exposure.natWeight D.exposure.natLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    D.exposure.hasReverseWeightBound
    (kernelLastPerm D.kernelCoordinate 1)
    (kernelLastPerm D.kernelCoordinate 3)
  simpa [QsRayFacetEndpointSourceExposure.reverseReesFamily] using hfamily

private theorem sourceMinor2_of_familyMinor
    (D : QsRayFacetEndpointFirstBreakData C)
    {j : ℕ}
    (h :
      let B := kernelLastFamilyHessianFourBlock
        D.exposure.reverseReesFamily D.kernelCoordinate
      (B.x * B.z - B.y * B.y).coeff j ≠ 0) :
    let rho := kernelLastPerm D.kernelCoordinate
    HC4.Polynomial.hessianPrincipalMinor
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
        (rho 2) (rho 3) ≠ 0 := by
  let rho := kernelLastPerm D.kernelCoordinate
  let B := kernelLastFamilyHessianFourBlock
    D.exposure.reverseReesFamily D.kernelCoordinate
  have hpoly : B.x * B.z - B.y * B.y ≠ 0 := by
    intro hz
    apply h
    dsimp only [B]
    rw [hz]
    simp
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 2) (rho 3)) ≠ 0 := by
    rw [← D.familyMinor2_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
          D.exposure.reverseReesFamily (rho 2) (rho 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  dsimp only [rho]
  apply reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    D.exposure.natWeight D.exposure.natLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    D.exposure.hasReverseWeightBound
    (kernelLastPerm D.kernelCoordinate 2)
    (kernelLastPerm D.kernelCoordinate 3)
  simpa [QsRayFacetEndpointSourceExposure.reverseReesFamily] using hfamily

private noncomputable def actualRankTwoChart0
    (D : QsRayFacetEndpointFirstBreakData C)
    (hminor :
      let rho := kernelLastPerm D.kernelCoordinate
      HC4.Polynomial.hessianPrincipalMinor
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
          (rho 0) (rho 3) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho := kernelLastPerm D.kernelCoordinate
  let sigma : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3
  let pi : Equiv.Perm (Fin 4) := sigma.trans rho
  refine {
    permutation := pi
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [pi, sigma, rho] using hminor

private noncomputable def actualRankTwoChart1
    (D : QsRayFacetEndpointFirstBreakData C)
    (hminor :
      let rho := kernelLastPerm D.kernelCoordinate
      HC4.Polynomial.hessianPrincipalMinor
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
          (rho 1) (rho 3) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho := kernelLastPerm D.kernelCoordinate
  let sigma : Equiv.Perm (Fin 4) :=
    (Equiv.swap (1 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)
  let pi : Equiv.Perm (Fin 4) := sigma.trans rho
  refine {
    permutation := pi
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [pi, sigma, rho] using hminor

private noncomputable def actualRankTwoChart2
    (D : QsRayFacetEndpointFirstBreakData C)
    (hminor :
      let rho := kernelLastPerm D.kernelCoordinate
      HC4.Polynomial.hessianPrincipalMinor
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
          (rho 2) (rho 3) ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho := kernelLastPerm D.kernelCoordinate
  let sigma : Equiv.Perm (Fin 4) :=
    (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)
  let pi : Equiv.Perm (Fin 4) := sigma.trans rho
  refine {
    permutation := pi
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [pi, sigma, rho] using hminor

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

end QsRayFacetEndpointFirstBreakData
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
