import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyRS2EulerMotion
import HC4.Newton.GeneralFourBlockKernelLift
import Mathlib.Tactic

/-!
# Final assembly A14: moving cleared-lift direction gives honest rank-two repair

A13 reduced the moving RS2 branch to a constant raw binary Schur line whose
four-component denominator-cleared lift has a genuinely moving projective
source direction.  This file turns that motion directly into a source-honest
rank-two derivative block.

Write `H` for the honest special-fibre Hessian four-block and `W` for the
cleared lift.  Polynomially,

    H W = 0.

At a point where both the chosen projective wedge and the active determinant
`Delta` are nonzero, differentiate in the wedge direction:

    (dH) W + H (dW) = 0.

Because the binary Schur line is constant, the last two coordinates of `W`
are `Delta * (u,v)`.  If `(dH)W` vanished, then `dW` would again lie in the
kernel of `H`; the invertible active `2 x 2` block and the last-coordinate
formula force `dW` to be a scalar multiple of `W`, contradicting the nonzero
projective wedge.  Hence `(dH)W != 0`.

Symmetry and `H W = 0` then give

    W^T (dH) W = 0.

Choosing a coordinate `t` with `((dH)W)_t != 0`, the restriction of `dH` to
`span{W,e_t}` has binary matrix

    [ 0  b ]
    [ b  c ]

with determinant `-b^2 != 0`.  This is an actual evaluated derivative-Hessian
rank-two source, retained together with the canonical repair progress before
it is fed to the existing exact-clock rank-two macro.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Evaluate the honest special-fibre four-block at one source point. -/
noncomputable def evaluatedSpecialMatrix
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (point : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  fun i j => MvPolynomial.eval point (C.specialFourBlock.matrix i j)

/-- Evaluate one honest source derivative of the special-fibre four-block. -/
noncomputable def evaluatedSpecialDerivativeMatrix
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4)
    (point : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  fun i j =>
    MvPolynomial.eval point
      (MvPolynomial.pderiv k (C.specialFourBlock.matrix i j))

namespace DenominatorClearedSpecialSchurKernelData

variable {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}

/-- Evaluate the denominator-cleared full kernel vector. -/
noncomputable def evaluatedFullVector
    (E : C.DenominatorClearedSpecialSchurKernelData)
    (point : Fin 4 → K) : Fin 4 → K :=
  fun i => MvPolynomial.eval point (E.fullVector i)

/-- Evaluate the source derivative of the denominator-cleared full kernel. -/
noncomputable def evaluatedFullVectorDerivative
    (E : C.DenominatorClearedSpecialSchurKernelData)
    (k : Fin 4)
    (point : Fin 4 → K) : Fin 4 → K :=
  fun i => MvPolynomial.eval point (MvPolynomial.pderiv k (E.fullVector i))

/-- Evaluation of one projective-wedge polynomial is the corresponding wedge
of the evaluated full vector and its source derivative.  Keeping this expansion
outside the large RS2 repair theorem avoids an expensive late simplification. -/
theorem eval_projectiveWedge
    (E : C.DenominatorClearedSpecialSchurKernelData)
    (point : Fin 4 → K)
    (i j k : Fin 4) :
    MvPolynomial.eval point (E.projectiveWedge i j k) =
      E.evaluatedFullVector point i * E.evaluatedFullVectorDerivative k point j -
        E.evaluatedFullVector point j * E.evaluatedFullVectorDerivative k point i := by
  simp [projectiveWedge, evaluatedFullVector, evaluatedFullVectorDerivative]

/-- Evaluation of the polynomial kernel identity. -/
theorem evaluatedFullVector_kernel
    (E : C.DenominatorClearedSpecialSchurKernelData)
    (point : Fin 4 → K) :
    (C.evaluatedSpecialMatrix point).mulVec
        (E.evaluatedFullVector point) = 0 := by
  funext r
  have hr := congrFun E.fullVector_kernel r
  have hev := congrArg (MvPolynomial.eval point) hr
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.evaluatedSpecialMatrix,
    evaluatedFullVector, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using hev

/-- Differentiate `H W = 0` and then evaluate. -/
theorem evaluatedFullVector_derivative_kernel_identity
    (E : C.DenominatorClearedSpecialSchurKernelData)
    (k : Fin 4)
    (point : Fin 4 → K) :
    (C.evaluatedSpecialDerivativeMatrix k point).mulVec
          (E.evaluatedFullVector point) +
        (C.evaluatedSpecialMatrix point).mulVec
          (E.evaluatedFullVectorDerivative k point) = 0 := by
  funext r
  have hr := congrFun E.fullVector_kernel r
  have hder := congrArg (MvPolynomial.pderiv k) hr
  have hev := congrArg (MvPolynomial.eval point) hder
  simp [AdaptiveAlignedSmithRankOneClosingSourceCarrier.evaluatedSpecialMatrix,
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.evaluatedSpecialDerivativeMatrix,
    evaluatedFullVector, evaluatedFullVectorDerivative,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hev ⊢
  ring_nf at hev ⊢
  exact hev

end DenominatorClearedSpecialSchurKernelData

/-- The evaluated derivative matrix is symmetric, because it is an honest
source derivative of the symmetric Hessian four-block. -/
theorem evaluatedSpecialDerivativeMatrix_symmetric
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4)
    (point : Fin 4 → K) :
    ∀ i j : Fin 4,
      C.evaluatedSpecialDerivativeMatrix k point i j =
        C.evaluatedSpecialDerivativeMatrix k point j i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [evaluatedSpecialDerivativeMatrix, GeneralFourBlock.matrix]

/-- A regular projective point: the selected full-kernel projective wedge and
the active `2 x 2` determinant are simultaneously nonzero. -/
structure ConstantSpecialSchurKernelLineRS2RegularProjectivePointData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)
    (i j k : Fin 4) where
  point : Fin 4 → K
  wedge_ne_zero :
    MvPolynomial.eval point
      (R.line.toDenominatorClearedSpecialSchurKernelData.projectiveWedge i j k) ≠ 0
  activeDet_ne_zero :
    MvPolynomial.eval point C.specialFourBlock.activeDet ≠ 0

/-- A nonzero projective wedge can be witnessed where the honest active block
is invertible as well. -/
theorem ConstantSpecialSchurKernelLineRS2ActiveProjectiveData.exists_regularProjectivePoint
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData}
    (M : C.ConstantSpecialSchurKernelLineRS2ActiveProjectiveData R) :
    Nonempty (C.ConstantSpecialSchurKernelLineRS2RegularProjectivePointData
      R M.i M.j M.k) := by
  let E := R.line.toDenominatorClearedSpecialSchurKernelData
  have hactive : C.specialFourBlock.activeDet ≠ 0 := by
    change
      (parameterConstantCoeffFourBlock C.chartData.schurData.block).activeDet ≠ 0
    rw [← parameterConstantCoeffFourBlock_activeDet]
    exact C.chartData.schurData.activeDet_coeff_zero_ne_zero
  have hprod : E.projectiveWedge M.i M.j M.k * C.specialFourBlock.activeDet ≠ 0 :=
    mul_ne_zero M.wedge_ne_zero hactive
  rcases exists_source_eval_ne_zero_of_ne_zero
      (E.projectiveWedge M.i M.j M.k * C.specialFourBlock.activeDet) hprod with
    ⟨point, hpoint⟩
  have hwedge : MvPolynomial.eval point (E.projectiveWedge M.i M.j M.k) ≠ 0 := by
    intro hzero
    apply hpoint
    simp [hzero]
  have hdet : MvPolynomial.eval point C.specialFourBlock.activeDet ≠ 0 := by
    intro hzero
    apply hpoint
    simp [hzero]
  exact ⟨{
    point := point
    wedge_ne_zero := hwedge
    activeDet_ne_zero := hdet
  }⟩

/-- Source-honest rank-two derivative packet extracted from motion of the
cleared full kernel.  The retained binary block is literally the restriction
of one evaluated source derivative of the honest special Hessian to the
isotropic kernel vector and one coordinate direction. -/
structure ConstantLineLiftDerivativeRankTwoRepairData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)
    (complexity : ℕ) where
  moving : C.ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData R
  regular :
    C.ConstantSpecialSchurKernelLineRS2RegularProjectivePointData
      R moving.moving.i moving.moving.j moving.moving.k
  pivot : Fin 4
  derivativeKernel_ne_zero :
    (C.evaluatedSpecialDerivativeMatrix moving.moving.k regular.point).mulVec
      (R.line.toDenominatorClearedSpecialSchurKernelData.evaluatedFullVector
        regular.point) ≠ 0
  pivot_ne_zero :
    ((C.evaluatedSpecialDerivativeMatrix moving.moving.k regular.point).mulVec
      (R.line.toDenominatorClearedSpecialSchurKernelData.evaluatedFullVector
        regular.point)) pivot ≠ 0
  isotropic :
    dotProduct
      (R.line.toDenominatorClearedSpecialSchurKernelData.evaluatedFullVector
        regular.point)
      ((C.evaluatedSpecialDerivativeMatrix moving.moving.k regular.point).mulVec
        (R.line.toDenominatorClearedSpecialSchurKernelData.evaluatedFullVector
          regular.point)) = 0
  derivative_symmetric :
    ∀ i j : Fin 4,
      C.evaluatedSpecialDerivativeMatrix moving.moving.k regular.point i j =
        C.evaluatedSpecialDerivativeMatrix moving.moving.k regular.point j i
  evaluatedBlock : BinarySchurBlock K
  evaluatedBlock_eq :
    evaluatedBlock = {
      a := dotProduct
        (R.line.toDenominatorClearedSpecialSchurKernelData.evaluatedFullVector
          regular.point)
        ((C.evaluatedSpecialDerivativeMatrix moving.moving.k regular.point).mulVec
          (R.line.toDenominatorClearedSpecialSchurKernelData.evaluatedFullVector
            regular.point))
      b := ((C.evaluatedSpecialDerivativeMatrix moving.moving.k regular.point).mulVec
        (R.line.toDenominatorClearedSpecialSchurKernelData.evaluatedFullVector
          regular.point)) pivot
      c := C.evaluatedSpecialDerivativeMatrix
        moving.moving.k regular.point pivot pivot
    }
  evaluatedBlock_detCore_ne_zero : evaluatedBlock.detCore ≠ 0
  evaluatedBlock_trivialKernel : evaluatedBlock.HasTrivialKernel
  progress :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity)
  measure_lt :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure

set_option maxHeartbeats 1000000 in
/-- A moving constant-line cleared lift exposes a genuine rank-two derivative
block of the honest source Hessian. -/
theorem ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData.exists_liftDerivativeRankTwoRepairData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData}
    (M0 : C.ConstantSpecialSchurKernelLineRS2ActiveEulerMotionData R)
    (complexity : ℕ) :
    Nonempty (C.ConstantLineLiftDerivativeRankTwoRepairData R complexity) := by
  let E := R.line.toDenominatorClearedSpecialSchurKernelData
  rcases M0.moving.exists_regularProjectivePoint with ⟨regular⟩
  let point := regular.point
  let k := M0.moving.k
  let H := C.evaluatedSpecialMatrix point
  let DH := C.evaluatedSpecialDerivativeMatrix k point
  let w := E.evaluatedFullVector point
  let dw := E.evaluatedFullVectorDerivative k point
  let delta := MvPolynomial.eval point C.specialFourBlock.activeDet
  let ddelta := MvPolynomial.eval point
    (MvPolynomial.pderiv k C.specialFourBlock.activeDet)
  let lam := ddelta / delta

  have hdelta : delta ≠ 0 := by
    simpa [delta] using regular.activeDet_ne_zero
  have hker : H.mulVec w = 0 := by
    simpa [H, w] using E.evaluatedFullVector_kernel point
  have hdiff : DH.mulVec w + H.mulVec dw = 0 := by
    simpa [H, DH, w, dw, k] using
      E.evaluatedFullVector_derivative_kernel_identity k point

  have hw2 : w (2 : Fin 4) = delta * R.line.u := by
    simp [w, E, DenominatorClearedSpecialSchurKernelData.evaluatedFullVector,
      DenominatorClearedSpecialSchurKernelData.fullVector,
      ConstantSpecialSchurKernelLineData.toDenominatorClearedSpecialSchurKernelData,
      GeneralFourBlock.clearedKernelLift, delta]
  have hw3 : w (3 : Fin 4) = delta * R.line.v := by
    simp [w, E, DenominatorClearedSpecialSchurKernelData.evaluatedFullVector,
      DenominatorClearedSpecialSchurKernelData.fullVector,
      ConstantSpecialSchurKernelLineData.toDenominatorClearedSpecialSchurKernelData,
      GeneralFourBlock.clearedKernelLift, delta]
  have hdw2raw : dw (2 : Fin 4) = ddelta * R.line.u := by
    simp [dw, E, DenominatorClearedSpecialSchurKernelData.evaluatedFullVectorDerivative,
      DenominatorClearedSpecialSchurKernelData.fullVector,
      ConstantSpecialSchurKernelLineData.toDenominatorClearedSpecialSchurKernelData,
      GeneralFourBlock.clearedKernelLift, ddelta, mul_comm]
  have hdw3raw : dw (3 : Fin 4) = ddelta * R.line.v := by
    simp [dw, E, DenominatorClearedSpecialSchurKernelData.evaluatedFullVectorDerivative,
      DenominatorClearedSpecialSchurKernelData.fullVector,
      ConstantSpecialSchurKernelLineData.toDenominatorClearedSpecialSchurKernelData,
      GeneralFourBlock.clearedKernelLift, ddelta, mul_comm]
  have hdw2 : dw (2 : Fin 4) = lam * w (2 : Fin 4) := by
    rw [hw2, hdw2raw]
    dsimp [lam]
    field_simp [hdelta] <;> ring
  have hdw3 : dw (3 : Fin 4) = lam * w (3 : Fin 4) := by
    rw [hw3, hdw3raw]
    dsimp [lam]
    field_simp [hdelta] <;> ring

  have hDHw : DH.mulVec w ≠ 0 := by
    intro hDHzero
    have hHdw : H.mulVec dw = 0 := by
      rw [hDHzero, zero_add] at hdiff
      exact hdiff

    let A := MvPolynomial.eval point C.specialFourBlock.a
    let BB := MvPolynomial.eval point C.specialFourBlock.b
    let DD := MvPolynomial.eval point C.specialFourBlock.d
    let z0 := dw (0 : Fin 4) - lam * w (0 : Fin 4)
    let z1 := dw (1 : Fin 4) - lam * w (1 : Fin 4)

    have hrow0dw := congrFun hHdw (0 : Fin 4)
    have hrow1dw := congrFun hHdw (1 : Fin 4)
    have hrow0w := congrFun hker (0 : Fin 4)
    have hrow1w := congrFun hker (1 : Fin 4)
    simp [H, evaluatedSpecialMatrix, GeneralFourBlock.matrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] at hrow0dw hrow1dw hrow0w hrow1w
    rw [hdw2, hdw3] at hrow0dw hrow1dw

    have hz0eq : A * z0 + BB * z1 = 0 := by
      dsimp [A, BB, z0, z1]
      linear_combination hrow0dw - lam * hrow0w
    have hz1eq : BB * z0 + DD * z1 = 0 := by
      dsimp [BB, DD, z0, z1]
      linear_combination hrow1dw - lam * hrow1w
    have hdeltaEq : delta = A * DD - BB * BB := by
      simp [delta, A, BB, DD, GeneralFourBlock.activeDet]
    have hz0prod : delta * z0 = 0 := by
      rw [hdeltaEq]
      linear_combination DD * hz0eq - BB * hz1eq
    have hz1prod : delta * z1 = 0 := by
      rw [hdeltaEq]
      linear_combination A * hz1eq - BB * hz0eq
    have hz0zero : z0 = 0 := (mul_eq_zero.mp hz0prod).resolve_left hdelta
    have hz1zero : z1 = 0 := (mul_eq_zero.mp hz1prod).resolve_left hdelta
    have hdw0 : dw (0 : Fin 4) = lam * w (0 : Fin 4) := by
      exact sub_eq_zero.mp (by simpa [z0] using hz0zero)
    have hdw1 : dw (1 : Fin 4) = lam * w (1 : Fin 4) := by
      exact sub_eq_zero.mp (by simpa [z1] using hz1zero)
    have hdwProp : dw = fun r => lam * w r := by
      funext r
      fin_cases r
      · exact hdw0
      · exact hdw1
      · exact hdw2
      · exact hdw3

    apply regular.wedge_ne_zero
    rw [DenominatorClearedSpecialSchurKernelData.eval_projectiveWedge
      E point M0.moving.i M0.moving.j M0.moving.k]
    change w M0.moving.i * dw M0.moving.j -
        w M0.moving.j * dw M0.moving.i = 0
    rw [congrFun hdwProp M0.moving.i, congrFun hdwProp M0.moving.j]
    ring

  have hdotSym :
      dotProduct w (H.mulVec dw) = dotProduct (H.mulVec w) dw := by
    simp [H, evaluatedSpecialMatrix, GeneralFourBlock.matrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring

  have hisotropic : dotProduct w (DH.mulVec w) = 0 := by
    have hDH_eq : DH.mulVec w = -(H.mulVec dw) := by
      exact eq_neg_of_add_eq_zero_left hdiff
    rw [hDH_eq]
    calc
      dotProduct w (-(H.mulVec dw)) = -dotProduct w (H.mulVec dw) := by
        simp [dotProduct, Fin.sum_univ_four]
      _ = -dotProduct (H.mulVec w) dw := by rw [hdotSym]
      _ = 0 := by rw [hker]; simp [dotProduct]

  have hpivotExists : ∃ t : Fin 4, (DH.mulVec w) t ≠ 0 := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    apply hDHw
    funext t
    exact hnone t
  rcases hpivotExists with ⟨pivot, hpivot⟩

  let block : BinarySchurBlock K := {
    a := dotProduct w (DH.mulVec w)
    b := (DH.mulVec w) pivot
    c := DH pivot pivot
  }
  have hblockdet : block.detCore ≠ 0 := by
    have hsq : (DH.mulVec w) pivot * (DH.mulVec w) pivot ≠ 0 :=
      mul_ne_zero hpivot hpivot
    have hneg : -((DH.mulVec w) pivot * (DH.mulVec w) pivot) ≠ 0 :=
      neg_ne_zero.mpr hsq
    simpa [block, BinarySchurBlock.detCore, hisotropic] using hneg
  have htrivial : block.HasTrivialKernel :=
    BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero block hblockdet
  have hprogress :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) :=
    rankOne_to_rankTwo_repairProgress complexity

  exact ⟨{
    moving := M0
    regular := regular
    pivot := pivot
    derivativeKernel_ne_zero := by simpa [DH, w] using hDHw
    pivot_ne_zero := by simpa [DH, w] using hpivot
    isotropic := by simpa [DH, w] using hisotropic
    derivative_symmetric := by
      simpa [DH, k, point] using C.evaluatedSpecialDerivativeMatrix_symmetric k point
    evaluatedBlock := block
    evaluatedBlock_eq := rfl
    evaluatedBlock_detCore_ne_zero := hblockdet
    evaluatedBlock_trivialKernel := htrivial
    progress := hprogress
    measure_lt := repairState_measure_lt_of_progress hprogress
  }⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- A14 terminal geometry: the moving RS2 lift has been consumed as rank-two
repair, so only the constant-source-kernel RS2 residue remains. -/
inductive AdaptiveAlignedSmithCanonicalRS2LiftRepairTerminalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop

  | rs2ConstantSourceKernel
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (hlt : C.firstActualLayerOrder < S.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder)
      (R : C.ConstantSpecialSchurKernelLineRS2PreassemblyData)
      (kernel :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.ConstantSpecialSourceKernelData C)

  | canonicalAxisCore
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (core :
        AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareAxisTerminalCoreData
          C heq)

  | zeroSchurSourceReady
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)

  | planarRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigid
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | sectionGaugeKilled
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hkilled :
        G.source.sectionGaugeRightSection G.index G.section_ne G.index = 0)

  | sectionGaugeOrderRaised
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier S.blocker)
      (heq : C.firstActualLayerOrder = S.blocker.aligned.endpoint.defect)
      (G : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingPositiveSectionGaugeStep C)
      (hnew : G.source.sectionGaugeRightSection G.index G.section_ne G.index ≠ 0)
      (hstrict :
        G.source.sectionGaugeOrder G.index G.section_ne <
          polynomialParameterOrder
            (G.source.sectionGaugeRightSection G.index G.section_ne G.index)
            hnew)

structure AdaptiveAlignedSmithCanonicalRS2LiftRepairTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalRS2LiftRepairTerminalGeometry stationary

inductive AdaptiveAlignedSmithCanonicalStationaryPlanarCoreRS2LiftRepairOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | rankTwoMacro
      (outer target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove outer s)
      (hprogress : CertifiedSameScaleEpisodeProgress RR target outer)

  | local
      (P : AdaptiveAlignedSmithCanonicalRS2LiftRepairTerminalLocalProblem s)

  | internalPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)
      (trace : AdaptiveAlignedSmithCanonicalPresentationTrace RR s target)

/-- **A14 moving-lift elimination.**

A13's active Euler/projective RS2 residue produces an honest nondegenerate
binary block inside a source derivative of the special-fibre Hessian.  Its
canonical repair progress is therefore consumed by the existing exact-clock
rank-two macro.  No corrected-RS2 coefficient identification is needed. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalStationaryPlanarCoreRS2LiftRepairFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalStationaryPlanarCoreRS2LiftRepairOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalStationaryPlanarCoreRS2EulerFrontier
      RR complexity hsrepair with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | ramifiedSpend target hspend =>
      exact .ramifiedSpend target hspend
  | rankTwoMacro outer target hmove hprogress =>
      exact .rankTwoMacro outer target hmove hprogress
  | internalPresentation target hmove trace =>
      exact .internalPresentation target hmove trace
  | «local» P =>
      cases P.geometry with
      | rs2ConstantSourceKernel C hlt htangential R kernel =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .rs2ConstantSourceKernel C hlt htangential R kernel
          }
      | rs2ActiveEulerSource C hlt htangential R moving =>
          rcases moving.exists_liftDerivativeRankTwoRepairData complexity with ⟨repair⟩
          rcases P.stationary.blocker.aligned.exists_outerRankTwoRepairMacro
              RR s complexity hsrepair P.clock_eq repair.progress with
            ⟨outer, target, hmove, hprogress⟩
          exact .rankTwoMacro outer target hmove hprogress
      | canonicalAxisCore C heq core =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .canonicalAxisCore C heq core
          }
      | zeroSchurSourceReady C source =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .zeroSchurSourceReady C source
          }
      | planarRigid hall Q hrigid =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .planarRigid hall Q hrigid
          }
      | wSquareRigid hall Q hrigid =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .wSquareRigid hall Q hrigid
          }
      | sectionGaugeKilled C heq G hkilled =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .sectionGaugeKilled C heq G hkilled
          }
      | sectionGaugeOrderRaised C heq G hnew hstrict =>
          exact .local {
            stationary := P.stationary
            clock_eq := P.clock_eq
            clock_pos := P.clock_pos
            source := P.source
            geometry := .sectionGaugeOrderRaised C heq G hnew hstrict
          }

end

end HC4.Valuation
