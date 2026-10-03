import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurTangentSplit
import Mathlib.Tactic

/-!
# Source-layer cross equation in the tangent three-Schur branch

At the physical first kernel-row opening order, the tangent branch says that
the cleared 1+3 Schur quotient still has zero kernel column.  Because the raw
kernel row has no coefficients below that first order, the coefficient
convolution collapses to its constant-times-first-layer terms.

Consequently, if p is the scalar Schur pivot and k is the stored top-face
kernel coordinate, then for every active kernel-last coordinate r,

    Hess(H_D)_{p,p} Hess(G_E)_{r,k}
      - Hess(H_D)_{p,r} Hess(G_E)_{p,k} = 0.

Here H_D is the literal maximal linear-power top face and G_E is the exact
lower ordinary source layer retained by the first break.

This is the source-honest tangent equation needed to cancel the common
linear-power Hessian factor in the next stage.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Kernel-last coordinate used as the scalar pivot of the chosen 1+3 Schur
clock.  It is always one of slots 0,1,2. -/
def TopKernelThreeSchurClockData.pivotSlot
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Fin 4 :=
  match S with
  | .pivotA _ _ _ => 0
  | .pivotD _ _ _ => 1
  | .pivotX _ _ _ => 2

@[simp] theorem TopKernelThreeSchurClockData.pivotSlot_pivotA
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {ha hzero hdet}
    : (TopKernelThreeSchurClockData.pivotA
        (P := P) ha hzero hdet).pivotSlot = 0 := rfl

@[simp] theorem TopKernelThreeSchurClockData.pivotSlot_pivotD
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {hd hzero hdet}
    : (TopKernelThreeSchurClockData.pivotD
        (P := P) hd hzero hdet).pivotSlot = 1 := rfl

@[simp] theorem TopKernelThreeSchurClockData.pivotSlot_pivotX
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {hx hzero hdet}
    : (TopKernelThreeSchurClockData.pivotX
        (P := P) hx hzero hdet).pivotSlot = 2 := rfl

/-- Exact lower source layer carried by a nonlinear mixed first break. -/
noncomputable def ExactNonlinearMixedOrdinaryLayerAtFirstBreak.sourceLayer
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    MvPolynomial (Fin 4) K :=
  HC4.Polynomial.initialForm
    (fun i => (ordinaryTopNatWeight i : ℤ))
    (M.mixed.layer.sourceDegree : ℤ)
    T.topKernelReesSource

/-- Coefficient of any kernel-last Hessian entry at the physical first-break
order is exactly the corresponding Hessian entry of the retained exact source
layer. -/
theorem ExactNonlinearMixedOrdinaryLayerAtFirstBreak.rawEntry_coeff_firstBreak
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
    (r s : Fin 4) :
    (kernelLastParameterFirstHessian
        T.topKernelReverseReesFamily kernelCoordinate r s).coeff
        M.mixed.layer.order =
      HC4.Polynomial.hessian M.sourceLayer
        (kernelLastPerm kernelCoordinate r)
        (kernelLastPerm kernelCoordinate s) := by
  unfold kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply]
  rw [parameterFirstHessian_coeff, M.mixed.layer.exactLayer]
  rfl

/-- The selected scalar pivot is genuinely nonzero on the literal top face. -/
theorem TopKernelThreeSchurClockData.topFace_pivotDiagonal_ne_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) :
    HC4.Polynomial.hessian T.topFace.face
      (kernelLastPerm kernelCoordinate S.pivotSlot)
      (kernelLastPerm kernelCoordinate S.pivotSlot) ≠ 0 := by
  cases S with
  | pivotA hpivot hzero hdet =>
      have h := P.threeSchurBlock_coeff_zero (0 : Fin 4) 0
      change P.threeSchurBlock.a.coeff 0 =
        HC4.Polynomial.hessian T.topFace.face
          (kernelLastPerm kernelCoordinate 0)
          (kernelLastPerm kernelCoordinate 0) at h
      rw [h] at hpivot
      simpa using hpivot
  | pivotD hpivot hzero hdet =>
      have h := P.threeSchurBlock_coeff_zero (1 : Fin 4) 1
      change P.threeSchurBlock.d.coeff 0 =
        HC4.Polynomial.hessian T.topFace.face
          (kernelLastPerm kernelCoordinate 1)
          (kernelLastPerm kernelCoordinate 1) at h
      rw [h] at hpivot
      simpa using hpivot
  | pivotX hpivot hzero hdet =>
      have h := P.threeSchurBlock_coeff_zero (2 : Fin 4) 2
      change P.threeSchurBlock.x.coeff 0 =
        HC4.Polynomial.hessian T.topFace.face
          (kernelLastPerm kernelCoordinate 2)
          (kernelLastPerm kernelCoordinate 2) at h
      rw [h] at hpivot
      simpa using hpivot

theorem firstBreak_kernelRow_lower_zero'
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    let B := kernelLastFamilyHessianFourBlock
      T.topKernelReverseReesFamily kernelCoordinate
    ∀ n : ℕ, n < M.mixed.layer.order →
      B.q.coeff n = 0 ∧ B.s.coeff n = 0 ∧
        B.y.coeff n = 0 ∧ B.z.coeff n = 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
  change ∀ n : ℕ, n < M.mixed.layer.order →
    B.q.coeff n = 0 ∧ B.s.coeff n = 0 ∧
      B.y.coeff n = 0 ∧ B.z.coeff n = 0
  intro n hn
  have horder :
      M.mixed.layer.order =
        firstFourBlockKernelRowBreakOrder B hrow := by
    simpa [B, hrow] using M.mixed.layer.order_is_firstBreak
  have hn' :
      n < firstFourBlockKernelRowBreakOrder B hrow := by
    rw [← horder]
    exact hn
  exact firstFourBlockKernelRowBreakOrder_lower_zero B hrow hn'

/-- **Source-layer tangent cross equation.**

For every active kernel-last slot r=0,1,2, the top Hessian pivot row and the
first lower source-layer kernel column satisfy the exact rank-one tangent
relation. -/
theorem ThreeSchurTangentAtFirstBreak.sourceLayer_cross_zero
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M)
    (r : Fin 3) :
    HC4.Polynomial.hessian T.topFace.face
          (kernelLastPerm kernelCoordinate S.pivotSlot)
          (kernelLastPerm kernelCoordinate S.pivotSlot) *
        HC4.Polynomial.hessian M.sourceLayer
          (kernelLastPerm kernelCoordinate r.castSucc)
          kernelCoordinate -
      HC4.Polynomial.hessian T.topFace.face
          (kernelLastPerm kernelCoordinate S.pivotSlot)
          (kernelLastPerm kernelCoordinate r.castSucc) *
        HC4.Polynomial.hessian M.sourceLayer
          (kernelLastPerm kernelCoordinate S.pivotSlot)
          kernelCoordinate = 0 := by
  let B := kernelLastFamilyHessianFourBlock
    T.topKernelReverseReesFamily kernelCoordinate
  let j := M.mixed.layer.order
  have hj : 0 < j := by
    simpa [j] using M.mixed.layer.order_pos
  have hlower := firstBreak_kernelRow_lower_zero' M
  have hqLower : ∀ n : ℕ, n < j → B.q.coeff n = 0 :=
    fun n hn => (hlower n (by simpa [j] using hn)).1
  have hsLower : ∀ n : ℕ, n < j → B.s.coeff n = 0 :=
    fun n hn => (hlower n (by simpa [j] using hn)).2.1
  have hyLower : ∀ n : ℕ, n < j → B.y.coeff n = 0 :=
    fun n hn => (hlower n (by simpa [j] using hn)).2.2.1

  cases S with
  | pivotA hpivot hzero hdet =>
      fin_cases r
      · simp
      · have ht := R.mixed0_zero
        change (B.a * B.s - B.b * B.q).coeff j = 0 at ht
        have has :
            (B.a * B.s).coeff j = B.a.coeff 0 * B.s.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.a B.s hsLower
        have hbq :
            (B.b * B.q).coeff j = B.b.coeff 0 * B.q.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.b B.q hqLower
        rw [Polynomial.coeff_sub, has, hbq] at ht
        have h00 := P.threeSchurBlock_coeff_zero (0 : Fin 4) 0
        have h01 := P.threeSchurBlock_coeff_zero (0 : Fin 4) 1
        have hs := M.rawEntry_coeff_firstBreak (1 : Fin 4) 3
        have hq := M.rawEntry_coeff_firstBreak (0 : Fin 4) 3
        change B.a.coeff 0 = _ at h00
        change B.b.coeff 0 = _ at h01
        change B.s.coeff j = _ at hs
        change B.q.coeff j = _ at hq
        rw [h00, h01, hs, hq] at ht
        simpa [kernelLastPerm_last, j, B] using ht
      · have ht := R.mixed1_zero
        change (B.a * B.y - B.p * B.q).coeff j = 0 at ht
        have hay :
            (B.a * B.y).coeff j = B.a.coeff 0 * B.y.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.a B.y hyLower
        have hpq :
            (B.p * B.q).coeff j = B.p.coeff 0 * B.q.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.p B.q hqLower
        rw [Polynomial.coeff_sub, hay, hpq] at ht
        have h00 := P.threeSchurBlock_coeff_zero (0 : Fin 4) 0
        have h02 := P.threeSchurBlock_coeff_zero (0 : Fin 4) 2
        have hy := M.rawEntry_coeff_firstBreak (2 : Fin 4) 3
        have hq := M.rawEntry_coeff_firstBreak (0 : Fin 4) 3
        change B.a.coeff 0 = _ at h00
        change B.p.coeff 0 = _ at h02
        change B.y.coeff j = _ at hy
        change B.q.coeff j = _ at hq
        rw [h00, h02, hy, hq] at ht
        simpa [kernelLastPerm_last, j, B] using ht
  | pivotD hpivot hzero hdet =>
      fin_cases r
      · have ht := R.mixed0_zero
        change (B.d * B.q - B.b * B.s).coeff j = 0 at ht
        have hdq :
            (B.d * B.q).coeff j = B.d.coeff 0 * B.q.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.d B.q hqLower
        have hbs :
            (B.b * B.s).coeff j = B.b.coeff 0 * B.s.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.b B.s hsLower
        rw [Polynomial.coeff_sub, hdq, hbs] at ht
        have h11 := P.threeSchurBlock_coeff_zero (1 : Fin 4) 1
        have h01 := P.threeSchurBlock_coeff_zero (0 : Fin 4) 1
        have hq := M.rawEntry_coeff_firstBreak (0 : Fin 4) 3
        have hs := M.rawEntry_coeff_firstBreak (1 : Fin 4) 3
        change B.d.coeff 0 = _ at h11
        change B.b.coeff 0 = _ at h01
        change B.q.coeff j = _ at hq
        change B.s.coeff j = _ at hs
        rw [h11, h01, hq, hs] at ht
        simpa [kernelLastPerm_last, j, B, HC4.Polynomial.hessian_apply,
          pderiv_comm_commRing] using ht
      · simp
      · have ht := R.mixed1_zero
        change (B.d * B.y - B.r * B.s).coeff j = 0 at ht
        have hdy :
            (B.d * B.y).coeff j = B.d.coeff 0 * B.y.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.d B.y hyLower
        have hrs :
            (B.r * B.s).coeff j = B.r.coeff 0 * B.s.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.r B.s hsLower
        rw [Polynomial.coeff_sub, hdy, hrs] at ht
        have h11 := P.threeSchurBlock_coeff_zero (1 : Fin 4) 1
        have h12 := P.threeSchurBlock_coeff_zero (1 : Fin 4) 2
        have hy := M.rawEntry_coeff_firstBreak (2 : Fin 4) 3
        have hs := M.rawEntry_coeff_firstBreak (1 : Fin 4) 3
        change B.d.coeff 0 = _ at h11
        change B.r.coeff 0 = _ at h12
        change B.y.coeff j = _ at hy
        change B.s.coeff j = _ at hs
        rw [h11, h12, hy, hs] at ht
        simpa [kernelLastPerm_last, j, B] using ht
  | pivotX hpivot hzero hdet =>
      fin_cases r
      · have ht := R.mixed0_zero
        change (B.x * B.q - B.p * B.y).coeff j = 0 at ht
        have hxq :
            (B.x * B.q).coeff j = B.x.coeff 0 * B.q.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.x B.q hqLower
        have hpy :
            (B.p * B.y).coeff j = B.p.coeff 0 * B.y.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.p B.y hyLower
        rw [Polynomial.coeff_sub, hxq, hpy] at ht
        have h22 := P.threeSchurBlock_coeff_zero (2 : Fin 4) 2
        have h02 := P.threeSchurBlock_coeff_zero (0 : Fin 4) 2
        have hq := M.rawEntry_coeff_firstBreak (0 : Fin 4) 3
        have hy := M.rawEntry_coeff_firstBreak (2 : Fin 4) 3
        change B.x.coeff 0 = _ at h22
        change B.p.coeff 0 = _ at h02
        change B.q.coeff j = _ at hq
        change B.y.coeff j = _ at hy
        rw [h22, h02, hq, hy] at ht
        simpa [kernelLastPerm_last, j, B, HC4.Polynomial.hessian_apply,
          pderiv_comm_commRing] using ht
      · have ht := R.mixed1_zero
        change (B.x * B.s - B.r * B.y).coeff j = 0 at ht
        have hxs :
            (B.x * B.s).coeff j = B.x.coeff 0 * B.s.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.x B.s hsLower
        have hry :
            (B.r * B.y).coeff j = B.r.coeff 0 * B.y.coeff j :=
          coeff_mul_eq_constant_mul_of_right_vanishes_below B.r B.y hyLower
        rw [Polynomial.coeff_sub, hxs, hry] at ht
        have h22 := P.threeSchurBlock_coeff_zero (2 : Fin 4) 2
        have h12 := P.threeSchurBlock_coeff_zero (1 : Fin 4) 2
        have hs := M.rawEntry_coeff_firstBreak (1 : Fin 4) 3
        have hy := M.rawEntry_coeff_firstBreak (2 : Fin 4) 3
        change B.x.coeff 0 = _ at h22
        change B.r.coeff 0 = _ at h12
        change B.s.coeff j = _ at hs
        change B.y.coeff j = _ at hy
        rw [h22, h12, hs, hy] at ht
        simpa [kernelLastPerm_last, j, B, HC4.Polynomial.hessian_apply,
          pderiv_comm_commRing] using ht
      · simp

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
