import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerFirstBreak
import HC4.Valuation.ReverseWeightedReesHessianPrincipalMinor
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Source lift for the zero-clock top-kernel first break

The top-kernel linear-power branch already reaches concrete rank-two geometry
at the first opening of the honest ordinary reverse-Rees kernel row.  The
generic first-break theorem has two outputs:

* a nonzero coefficient of a whole-family principal Hessian minor; or
* a principal Hessian minor living entirely in the first breaking layer.

The first output is already strong enough to lift through reverse Rees to the
literal represented determinant-one source.  This file performs that lift and
packages the resulting source minor as the existing actual-rank-two Hessian
chart.

The layer-only output is retained source-honestly as an *exact ordinary
homogeneous component* of the represented source.  Its degree is strictly
below the maximal singular top degree, because the kernel row genuinely breaks
at positive reverse-Rees order.

Thus callers no longer see an opaque auxiliary Rees event.  They see either

1. actual rank-two geometry on the represented source; or
2. a concrete lower ordinary source layer carrying a nonzero principal
   Hessian minor.

No auxiliary Rees order is identified with the zero blocker clock, and no
repair transition or terminality hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Parameter-first transport of a principal Hessian minor, with symmetry used
to write the cross term as a square.  This local helper is intentionally
duplicated from the lower-ray endpoint source-lift module so this top-kernel
module does not depend on a private declaration in an unrelated namespace. -/
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

/-- Field-valued principal-minor square form. -/
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

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The stored zero coefficient of the top linear form really makes the
selected coordinate a Hessian-kernel coordinate of the top face. -/
theorem topFace_kernel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    MvPolynomial.pderiv kernelCoordinate T.topFace.face = 0 := by
  rw [P.eq_power, MvPolynomial.pderiv_C_mul]
  have hformula :=
    pderiv_gradientRatioLinearForm_pow_succ
      P.ratio kernelCoordinate (T.topFace.degree - 1)
  have hmrepr :
      T.topFace.degree - 1 + 1 = T.topFace.degree := by
    have hm3 : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
    omega
  rw [hmrepr] at hformula
  rw [hformula, P.kernel_ratio_zero]
  simp

/-- A source-facing exact ordinary layer left by the layer-only first-break
branch.  The layer is an exact ordinary component of the represented source,
strictly below the maximal top degree, and it carries a nonzero principal
minor involving the stored kernel coordinate. -/
structure ExactOrdinaryLayerMinorAtFirstBreak
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  order : ℕ
  order_is_firstBreak :
    order =
      firstFourBlockKernelRowBreakOrder
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate)
        (T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate)
  order_pos : 0 < order
  order_le_top : order ≤ T.topFace.degree
  sourceDegree : ℕ
  sourceDegree_eq : sourceDegree = T.topFace.degree - order
  sourceDegree_lt_top : sourceDegree < T.topFace.degree
  index : Fin 4
  index_ne_kernel : index ≠ kernelCoordinate
  exactLayer :
    familyParameterLayer T.topKernelReverseReesFamily order =
      HC4.Polynomial.initialForm
        (fun i => (ordinaryTopNatWeight i : ℤ))
        (sourceDegree : ℤ)
        T.topKernelReesSource
  minor_ne_zero :
    HC4.Polynomial.hessianPrincipalMinor
      (HC4.Polynomial.initialForm
        (fun i => (ordinaryTopNatWeight i : ℤ))
        (sourceDegree : ℤ)
        T.topKernelReesSource)
      index kernelCoordinate ≠ 0

private theorem familyMinor0_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.a * B.z - B.q * B.q =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 0)
          (kernelLastPerm kernelCoordinate 3)) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square
      T.topKernelReverseReesFamily
      (kernelLastPerm kernelCoordinate 0)
      (kernelLastPerm kernelCoordinate 3)).symm

private theorem familyMinor1_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.d * B.z - B.s * B.s =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 1)
          (kernelLastPerm kernelCoordinate 3)) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square
      T.topKernelReverseReesFamily
      (kernelLastPerm kernelCoordinate 1)
      (kernelLastPerm kernelCoordinate 3)).symm

private theorem familyMinor2_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.x * B.z - B.y * B.y =
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 2)
          (kernelLastPerm kernelCoordinate 3)) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  exact
    (parameterFirstEquiv_hessianPrincipalMinor_eq_square
      T.topKernelReverseReesFamily
      (kernelLastPerm kernelCoordinate 2)
      (kernelLastPerm kernelCoordinate 3)).symm

private theorem layerMinor0_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer T.topKernelReverseReesFamily j)
        (kernelLastPerm kernelCoordinate 0)
        (kernelLastPerm kernelCoordinate 3) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff]
  rw [hessianPrincipalMinor_eq_square]

private theorem layerMinor1_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer T.topKernelReverseReesFamily j)
        (kernelLastPerm kernelCoordinate 1)
        (kernelLastPerm kernelCoordinate 3) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff]
  rw [hessianPrincipalMinor_eq_square]

private theorem layerMinor2_eq
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer T.topKernelReverseReesFamily j)
        (kernelLastPerm kernelCoordinate 2)
        (kernelLastPerm kernelCoordinate 3) := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff]
  rw [hessianPrincipalMinor_eq_square]

private theorem layerMinor0_eq_kernel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer T.topKernelReverseReesFamily j)
        (kernelLastPerm kernelCoordinate 0) kernelCoordinate := by
  simpa only [kernelLastPerm_last] using P.layerMinor0_eq j

private theorem layerMinor1_eq_kernel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer T.topKernelReverseReesFamily j)
        (kernelLastPerm kernelCoordinate 1) kernelCoordinate := by
  simpa only [kernelLastPerm_last] using P.layerMinor1_eq j

private theorem layerMinor2_eq_kernel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer T.topKernelReverseReesFamily j)
        (kernelLastPerm kernelCoordinate 2) kernelCoordinate := by
  simpa only [kernelLastPerm_last] using P.layerMinor2_eq j

private theorem activeIndex0_ne_kernel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    kernelLastPerm kernelCoordinate (0 : Fin 4) ≠ kernelCoordinate := by
  intro h
  have h' :
      kernelLastPerm kernelCoordinate (0 : Fin 4) =
        kernelLastPerm kernelCoordinate (3 : Fin 4) := by
    simpa only [kernelLastPerm_last] using h
  have h03 : (0 : Fin 4) = (3 : Fin 4) :=
    (kernelLastPerm kernelCoordinate).injective h'
  exact (by decide : (0 : Fin 4) ≠ 3) h03

private theorem activeIndex1_ne_kernel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    kernelLastPerm kernelCoordinate (1 : Fin 4) ≠ kernelCoordinate := by
  intro h
  have h' :
      kernelLastPerm kernelCoordinate (1 : Fin 4) =
        kernelLastPerm kernelCoordinate (3 : Fin 4) := by
    simpa only [kernelLastPerm_last] using h
  have h13 : (1 : Fin 4) = (3 : Fin 4) :=
    (kernelLastPerm kernelCoordinate).injective h'
  exact (by decide : (1 : Fin 4) ≠ 3) h13

private theorem activeIndex2_ne_kernel
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    kernelLastPerm kernelCoordinate (2 : Fin 4) ≠ kernelCoordinate := by
  intro h
  have h' :
      kernelLastPerm kernelCoordinate (2 : Fin 4) =
        kernelLastPerm kernelCoordinate (3 : Fin 4) := by
    simpa only [kernelLastPerm_last] using h
  have h23 : (2 : Fin 4) = (3 : Fin 4) :=
    (kernelLastPerm kernelCoordinate).injective h'
  exact (by decide : (2 : Fin 4) ≠ 3) h23

private theorem sourceMinor0_of_familyMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {j : ℕ}
    (h :
      ((kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).a *
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).z -
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).q *
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).q).coeff j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
      T.topKernelReesSource
      (kernelLastPerm kernelCoordinate 0) kernelCoordinate ≠ 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  have hpoly : B.a * B.z - B.q * B.q ≠ 0 := by
    intro hz
    apply h
    have hc := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff j) hz
    simpa [B] using hc
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 0)
          (kernelLastPerm kernelCoordinate 3)) ≠ 0 := by
    rw [← P.familyMinor0_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
        T.topKernelReverseReesFamily
        (kernelLastPerm kernelCoordinate 0)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  have hlift :=
    reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
      ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound
      (kernelLastPerm kernelCoordinate 0)
      (kernelLastPerm kernelCoordinate 3)
      (by
        simpa [topKernelReverseReesFamily] using hfamily)
  simpa only [kernelLastPerm_last] using hlift

private theorem sourceMinor1_of_familyMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {j : ℕ}
    (h :
      ((kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).d *
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).z -
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).s *
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).s).coeff j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
      T.topKernelReesSource
      (kernelLastPerm kernelCoordinate 1) kernelCoordinate ≠ 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  have hpoly : B.d * B.z - B.s * B.s ≠ 0 := by
    intro hz
    apply h
    have hc := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff j) hz
    simpa [B] using hc
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 1)
          (kernelLastPerm kernelCoordinate 3)) ≠ 0 := by
    rw [← P.familyMinor1_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
        T.topKernelReverseReesFamily
        (kernelLastPerm kernelCoordinate 1)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  have hlift :=
    reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
      ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound
      (kernelLastPerm kernelCoordinate 1)
      (kernelLastPerm kernelCoordinate 3)
      (by
        simpa [topKernelReverseReesFamily] using hfamily)
  simpa only [kernelLastPerm_last] using hlift

private theorem sourceMinor2_of_familyMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    {j : ℕ}
    (h :
      ((kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).x *
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).z -
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).y *
        (kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate).y).coeff j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor
      T.topKernelReesSource
      (kernelLastPerm kernelCoordinate 2) kernelCoordinate ≠ 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  have hpoly : B.x * B.z - B.y * B.y ≠ 0 := by
    intro hz
    apply h
    have hc := congrArg
      (fun p : Polynomial (MvPolynomial (Fin 4) K) => p.coeff j) hz
    simpa [B] using hc
  have hparam :
      parameterFirstEquiv K
        (HC4.Polynomial.hessianPrincipalMinor
          T.topKernelReverseReesFamily
          (kernelLastPerm kernelCoordinate 2)
          (kernelLastPerm kernelCoordinate 3)) ≠ 0 := by
    rw [← P.familyMinor2_eq]
    exact hpoly
  have hfamily :
      HC4.Polynomial.hessianPrincipalMinor
        T.topKernelReverseReesFamily
        (kernelLastPerm kernelCoordinate 2)
        (kernelLastPerm kernelCoordinate 3) ≠ 0 := by
    intro hz
    apply hparam
    rw [hz]
    simp
  have hlift :=
    reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
      ordinaryTopNatWeight T.topFace.degree T.topKernelReesSource
      T.topKernelReesSource_hasReverseWeightBound
      (kernelLastPerm kernelCoordinate 2)
      (kernelLastPerm kernelCoordinate 3)
      (by
        simpa [topKernelReverseReesFamily] using hfamily)
  simpa only [kernelLastPerm_last] using hlift

private noncomputable def actualRankTwoChart0
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        T.topKernelReesSource
        (kernelLastPerm kernelCoordinate 0) kernelCoordinate ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  apply actualRankTwoHessianChart_of_specialFiber_minor
    (P.activeIndex0_ne_kernel)
  simpa [topKernelReesSource] using hminor

private noncomputable def actualRankTwoChart1
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        T.topKernelReesSource
        (kernelLastPerm kernelCoordinate 1) kernelCoordinate ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  apply actualRankTwoHessianChart_of_specialFiber_minor
    (P.activeIndex1_ne_kernel)
  simpa [topKernelReesSource] using hminor

private noncomputable def actualRankTwoChart2
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        T.topKernelReesSource
        (kernelLastPerm kernelCoordinate 2) kernelCoordinate ≠ 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  apply actualRankTwoHessianChart_of_specialFiber_minor
    (P.activeIndex2_ne_kernel)
  simpa [topKernelReesSource] using hminor

private theorem firstBreakOrder_pos
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
    0 < firstFourBlockKernelRowBreakOrder B hrow := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
  have hzero :=
    T.topKernelLastBlock_kernelRow_coeff_zero
      kernelCoordinate P.topFace_kernel
  exact firstFourBlockKernelRowBreakOrder_pos
    B hrow hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2

private theorem exactLayerData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (which : Fin 3)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer T.topKernelReverseReesFamily
          (firstFourBlockKernelRowBreakOrder
            (kernelLastFamilyHessianFourBlock
              T.topKernelReverseReesFamily kernelCoordinate)
            (T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate)))
        (kernelLastPerm kernelCoordinate which.castSucc)
        kernelCoordinate ≠ 0) :
    Nonempty P.ExactOrdinaryLayerMinorAtFirstBreak := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow
  let L := familyParameterLayer T.topKernelReverseReesFamily j
  have hLne : L ≠ 0 := by
    intro hzero
    apply hminor
    rw [show
      familyParameterLayer T.topKernelReverseReesFamily
          (firstFourBlockKernelRowBreakOrder B hrow) = L by rfl]
    rw [hzero]
    simp [HC4.Polynomial.hessianPrincipalMinor,
      HC4.Polynomial.hessian_apply]
  have hexact :=
    reverseWeightedReesFamily_parameterLayer_eq_initialForm_of_ne_zero
      ordinaryTopNatWeight T.topFace.degree j
      T.topKernelReesSource T.topKernelReesSource_hasReverseWeightBound
      (by
        simpa [L, topKernelReverseReesFamily] using hLne)
  have hjle : j ≤ T.topFace.degree := hexact.1
  have hjpos : 0 < j := by
    dsimp [j, B, hrow]
    exact P.firstBreakOrder_pos
  let E := T.topFace.degree - j
  have hElt : E < T.topFace.degree := by
    dsimp [E]
    have hD3 : 3 ≤ T.topFace.degree := T.topFace.degree_ge_three
    omega
  have hidx :
      kernelLastPerm kernelCoordinate which.castSucc ≠ kernelCoordinate := by
    fin_cases which
    · simpa using P.activeIndex0_ne_kernel
    · simpa using P.activeIndex1_ne_kernel
    · simpa using P.activeIndex2_ne_kernel
  have hlayer :
      L =
        HC4.Polynomial.initialForm
          (fun i => (ordinaryTopNatWeight i : ℤ))
          (E : ℤ) T.topKernelReesSource := by
    have h := hexact.2
    simpa [L, topKernelReverseReesFamily, E] using h
  have hminor' :
      HC4.Polynomial.hessianPrincipalMinor
        (HC4.Polynomial.initialForm
          (fun i => (ordinaryTopNatWeight i : ℤ))
          (E : ℤ) T.topKernelReesSource)
        (kernelLastPerm kernelCoordinate which.castSucc)
        kernelCoordinate ≠ 0 := by
    rw [← hlayer]
    simpa [L, j, B, hrow] using hminor
  exact ⟨{
    order := j
    order_is_firstBreak := rfl
    order_pos := hjpos
    order_le_top := hjle
    sourceDegree := E
    sourceDegree_eq := rfl
    sourceDegree_lt_top := hElt
    index := kernelLastPerm kernelCoordinate which.castSucc
    index_ne_kernel := hidx
    exactLayer := hlayer
    minor_ne_zero := hminor'
  }⟩

/-- **Source-honest top-kernel first-break frontier.**

The whole-family branch is an actual rank-two Hessian chart on the represented
determinant-one source.  The only residual branch is a nonzero principal minor
on an exact lower ordinary homogeneous component of that same source. -/
theorem actualRankTwo_or_exactLowerOrdinaryLayerMinor
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactOrdinaryLayerMinorAtFirstBreak := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow
  have hout := P.firstBreakRankTwoOutcome
  change RankOneSpecialFiberFirstBreakOutcome B j at hout
  cases hout with
  | familyMinor h =>
      rcases h with h0 | h1 | h2
      · exact Or.inl ⟨P.actualRankTwoChart0
          (P.sourceMinor0_of_familyMinor (j := j) h0)⟩
      · exact Or.inl ⟨P.actualRankTwoChart1
          (P.sourceMinor1_of_familyMinor (j := j) h1)⟩
      · exact Or.inl ⟨P.actualRankTwoChart2
          (P.sourceMinor2_of_familyMinor (j := j) h2)⟩
  | layerMinor h =>
      have hminor :
          HC4.Polynomial.hessianPrincipalMinor
              (familyParameterLayer T.topKernelReverseReesFamily j)
              (kernelLastPerm kernelCoordinate 0) kernelCoordinate ≠ 0 ∨
            HC4.Polynomial.hessianPrincipalMinor
              (familyParameterLayer T.topKernelReverseReesFamily j)
              (kernelLastPerm kernelCoordinate 1) kernelCoordinate ≠ 0 ∨
            HC4.Polynomial.hessianPrincipalMinor
              (familyParameterLayer T.topKernelReverseReesFamily j)
              (kernelLastPerm kernelCoordinate 2) kernelCoordinate ≠ 0 := by
        rcases h with h0 | h1 | h2
        · left
          rw [← P.layerMinor0_eq_kernel j]
          simpa only [kernelLastPerm_last] using h0
        · right
          left
          rw [← P.layerMinor1_eq_kernel j]
          simpa only [kernelLastPerm_last] using h1
        · right
          right
          rw [← P.layerMinor2_eq_kernel j]
          simpa only [kernelLastPerm_last] using h2
      rcases hminor with h0 | h1 | h2
      · exact Or.inr (P.exactLayerData (0 : Fin 3) (by
          simpa [j, B, hrow] using h0))
      · exact Or.inr (P.exactLayerData (1 : Fin 3) (by
          simpa [j, B, hrow] using h1))
      · exact Or.inr (P.exactLayerData (2 : Fin 3) (by
          simpa [j, B, hrow] using h2))


/-! ## Detailed mixed-opening frontier -/

/-- Source-honest refinement of the layer-only first-break branch.

Unlike `ExactOrdinaryLayerMinorAtFirstBreak`, this packet retains the exact
reason the first break was layer-only: the kernel diagonal is still zero on
that layer while one mixed kernel entry is nonzero. -/
structure ExactMixedOrdinaryLayerAtFirstBreak
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  layer : P.ExactOrdinaryLayerMinorAtFirstBreak
  kernelDiagonal_eq_zero :
    HC4.Polynomial.hessian
      (HC4.Polynomial.initialForm
        (fun i => (ordinaryTopNatWeight i : ℤ))
        (layer.sourceDegree : ℤ)
        T.topKernelReesSource)
      kernelCoordinate kernelCoordinate = 0
  mixed_ne_zero :
    HC4.Polynomial.hessian
      (HC4.Polynomial.initialForm
        (fun i => (ordinaryTopNatWeight i : ℤ))
        (layer.sourceDegree : ℤ)
        T.topKernelReesSource)
      layer.index kernelCoordinate ≠ 0

/-- **Detailed top-kernel first-break source lift.**

At the first opening of the kernel row, either the kernel diagonal itself
opens.  Then one nonzero active special-fibre diagonal gives a nonzero
whole-family principal minor at exactly that order, which lifts to an actual
rank-two chart on the represented source.

Or the kernel diagonal is still zero.  Then the first opening is genuinely
mixed, and the retained exact lower ordinary source layer satisfies
`H_kk = 0` but `H_ik != 0` for one transverse index `i`.

This keeps precisely the information needed by the mixed-layer
direction-lock/staircase algebra. -/
theorem actualRankTwo_or_exactLowerMixedOrdinaryLayer
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactMixedOrdinaryLayerAtFirstBreak := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
  let j := firstFourBlockKernelRowBreakOrder B hrow

  have hzero :=
    T.topKernelLastBlock_kernelRow_coeff_zero
      kernelCoordinate P.topFace_kernel
  have hjpos : 0 < j := by
    dsimp [j, B, hrow]
    exact firstFourBlockKernelRowBreakOrder_pos
      (kernelLastFamilyHessianFourBlock
        T.topKernelReverseReesFamily kernelCoordinate)
      (T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate)
      hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2
  have hlower :
      ∀ n : ℕ, n < j →
        B.q.coeff n = 0 ∧ B.s.coeff n = 0 ∧
          B.y.coeff n = 0 ∧ B.z.coeff n = 0 := by
    intro n hn
    dsimp [j] at hn
    exact firstFourBlockKernelRowBreakOrder_lower_zero B hrow hn
  have hqLower : ∀ n : ℕ, n < j → B.q.coeff n = 0 :=
    fun n hn => (hlower n hn).1
  have hsLower : ∀ n : ℕ, n < j → B.s.coeff n = 0 :=
    fun n hn => (hlower n hn).2.1
  have hyLower : ∀ n : ℕ, n < j → B.y.coeff n = 0 :=
    fun n hn => (hlower n hn).2.2.1
  have hzLower : ∀ n : ℕ, n < j → B.z.coeff n = 0 :=
    fun n hn => (hlower n hn).2.2.2
  have hbreak : fourBlockKernelRowBreakAt B j := by
    dsimp [j]
    exact firstFourBlockKernelRowBreakOrder_spec B hrow

  by_cases hzj : B.z.coeff j = 0
  · have hmixed :
        B.q.coeff j ≠ 0 ∨ B.s.coeff j ≠ 0 ∨ B.y.coeff j ≠ 0 := by
      rcases hbreak with hq | hs | hy | hz
      · exact Or.inl hq
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr hy)
      · exact (hz hzj).elim

    rcases hmixed with hq | hs | hy
    · have hminor :
          HC4.Polynomial.hessianPrincipalMinor
            (familyParameterLayer T.topKernelReverseReesFamily j)
            (kernelLastPerm kernelCoordinate 0) kernelCoordinate ≠ 0 := by
        rw [← P.layerMinor0_eq_kernel j]
        rw [hzj]
        simpa using neg_ne_zero.mpr (mul_ne_zero hq hq)
      rcases P.exactLayerData (0 : Fin 3) hminor with ⟨L⟩
      have horder : L.order = j := by
        simpa [j, B, hrow] using L.order_is_firstBreak
      have hdiag :
          HC4.Polynomial.hessian
            (HC4.Polynomial.initialForm
              (fun i => (ordinaryTopNatWeight i : ℤ))
              (L.sourceDegree : ℤ)
              T.topKernelReesSource)
            kernelCoordinate kernelCoordinate = 0 := by
        have hz :
            (parameterFirstHessian T.topKernelReverseReesFamily
              kernelCoordinate kernelCoordinate).coeff L.order = 0 := by
          rw [horder]
          simpa [B, kernelLastFamilyHessianFourBlock,
            GeneralFourBlock.ofSymmetricMatrix,
            kernelLastParameterFirstHessian] using hzj
        rw [parameterFirstHessian_coeff, L.exactLayer] at hz
        exact hz
      have hmix :
          HC4.Polynomial.hessian
            (HC4.Polynomial.initialForm
              (fun i => (ordinaryTopNatWeight i : ℤ))
              (L.sourceDegree : ℤ)
              T.topKernelReesSource)
            L.index kernelCoordinate ≠ 0 := by
        intro hzero
        apply L.minor_ne_zero
        rw [hessianPrincipalMinor_eq_square, hdiag, hzero]
        ring
      exact Or.inr ⟨{
        layer := L
        kernelDiagonal_eq_zero := hdiag
        mixed_ne_zero := hmix
      }⟩

    · have hminor :
          HC4.Polynomial.hessianPrincipalMinor
            (familyParameterLayer T.topKernelReverseReesFamily j)
            (kernelLastPerm kernelCoordinate 1) kernelCoordinate ≠ 0 := by
        rw [← P.layerMinor1_eq_kernel j]
        rw [hzj]
        simpa using neg_ne_zero.mpr (mul_ne_zero hs hs)
      rcases P.exactLayerData (1 : Fin 3) hminor with ⟨L⟩
      have horder : L.order = j := by
        simpa [j, B, hrow] using L.order_is_firstBreak
      have hdiag :
          HC4.Polynomial.hessian
            (HC4.Polynomial.initialForm
              (fun i => (ordinaryTopNatWeight i : ℤ))
              (L.sourceDegree : ℤ)
              T.topKernelReesSource)
            kernelCoordinate kernelCoordinate = 0 := by
        have hz :
            (parameterFirstHessian T.topKernelReverseReesFamily
              kernelCoordinate kernelCoordinate).coeff L.order = 0 := by
          rw [horder]
          simpa [B, kernelLastFamilyHessianFourBlock,
            GeneralFourBlock.ofSymmetricMatrix,
            kernelLastParameterFirstHessian] using hzj
        rw [parameterFirstHessian_coeff, L.exactLayer] at hz
        exact hz
      have hmix :
          HC4.Polynomial.hessian
            (HC4.Polynomial.initialForm
              (fun i => (ordinaryTopNatWeight i : ℤ))
              (L.sourceDegree : ℤ)
              T.topKernelReesSource)
            L.index kernelCoordinate ≠ 0 := by
        intro hzero
        apply L.minor_ne_zero
        rw [hessianPrincipalMinor_eq_square, hdiag, hzero]
        ring
      exact Or.inr ⟨{
        layer := L
        kernelDiagonal_eq_zero := hdiag
        mixed_ne_zero := hmix
      }⟩

    · have hminor :
          HC4.Polynomial.hessianPrincipalMinor
            (familyParameterLayer T.topKernelReverseReesFamily j)
            (kernelLastPerm kernelCoordinate 2) kernelCoordinate ≠ 0 := by
        rw [← P.layerMinor2_eq_kernel j]
        rw [hzj]
        simpa using neg_ne_zero.mpr (mul_ne_zero hy hy)
      rcases P.exactLayerData (2 : Fin 3) hminor with ⟨L⟩
      have horder : L.order = j := by
        simpa [j, B, hrow] using L.order_is_firstBreak
      have hdiag :
          HC4.Polynomial.hessian
            (HC4.Polynomial.initialForm
              (fun i => (ordinaryTopNatWeight i : ℤ))
              (L.sourceDegree : ℤ)
              T.topKernelReesSource)
            kernelCoordinate kernelCoordinate = 0 := by
        have hz :
            (parameterFirstHessian T.topKernelReverseReesFamily
              kernelCoordinate kernelCoordinate).coeff L.order = 0 := by
          rw [horder]
          simpa [B, kernelLastFamilyHessianFourBlock,
            GeneralFourBlock.ofSymmetricMatrix,
            kernelLastParameterFirstHessian] using hzj
        rw [parameterFirstHessian_coeff, L.exactLayer] at hz
        exact hz
      have hmix :
          HC4.Polynomial.hessian
            (HC4.Polynomial.initialForm
              (fun i => (ordinaryTopNatWeight i : ℤ))
              (L.sourceDegree : ℤ)
              T.topKernelReesSource)
            L.index kernelCoordinate ≠ 0 := by
        intro hzero
        apply L.minor_ne_zero
        rw [hessianPrincipalMinor_eq_square, hdiag, hzero]
        ring
      exact Or.inr ⟨{
        layer := L
        kernelDiagonal_eq_zero := hdiag
        mixed_ne_zero := hmix
      }⟩

  · have hqSq : (B.q * B.q).coeff j = 0 :=
      coeff_kernelPair_eq_zero_through B.q B.q hjpos hqLower hqLower j le_rfl
    have hsSq : (B.s * B.s).coeff j = 0 :=
      coeff_kernelPair_eq_zero_through B.s B.s hjpos hsLower hsLower j le_rfl
    have hySq : (B.y * B.y).coeff j = 0 :=
      coeff_kernelPair_eq_zero_through B.y B.y hjpos hyLower hyLower j le_rfl
    have haz : (B.a * B.z).coeff j = B.a.coeff 0 * B.z.coeff j :=
      coeff_mul_eq_constant_mul_of_right_vanishes_below B.a B.z hzLower
    have hdz : (B.d * B.z).coeff j = B.d.coeff 0 * B.z.coeff j :=
      coeff_mul_eq_constant_mul_of_right_vanishes_below B.d B.z hzLower
    have hxz : (B.x * B.z).coeff j = B.x.coeff 0 * B.z.coeff j :=
      coeff_mul_eq_constant_mul_of_right_vanishes_below B.x B.z hzLower
    have hactive :=
      P.kernelLastBlock_activeDiagonal_coeff_zero_ne_zero
    change B.a.coeff 0 ≠ 0 ∨ B.d.coeff 0 ≠ 0 ∨ B.x.coeff 0 ≠ 0 at hactive
    rcases hactive with ha | hd | hx
    · have hfamily :
          (B.a * B.z - B.q * B.q).coeff j ≠ 0 := by
        rw [Polynomial.coeff_sub, haz, hqSq]
        simpa using mul_ne_zero ha hzj
      exact Or.inl ⟨P.actualRankTwoChart0
        (P.sourceMinor0_of_familyMinor (j := j) hfamily)⟩
    · have hfamily :
          (B.d * B.z - B.s * B.s).coeff j ≠ 0 := by
        rw [Polynomial.coeff_sub, hdz, hsSq]
        simpa using mul_ne_zero hd hzj
      exact Or.inl ⟨P.actualRankTwoChart1
        (P.sourceMinor1_of_familyMinor (j := j) hfamily)⟩
    · have hfamily :
          (B.x * B.z - B.y * B.y).coeff j ≠ 0 := by
        rw [Polynomial.coeff_sub, hxz, hySq]
        simpa using mul_ne_zero hx hzj
      exact Or.inl ⟨P.actualRankTwoChart2
        (P.sourceMinor2_of_familyMinor (j := j) hfamily)⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
