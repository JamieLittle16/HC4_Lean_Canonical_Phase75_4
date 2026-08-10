import HC4.Valuation.RigidClosingRecenteredFirstKernelAssembly
import HC4.Valuation.KernelInflationHessianDefect
import Mathlib.Tactic

/-!
# Residual orientation after the first global rigid-closing kernel stage

Once the rigid Schur clock has been rebuilt on the recentered family, a
successful first global kernel blow-up and the local zero-Schur clock refer to
the same polynomial family.

The common first kernel is source coordinate `3`.  Reinflating an integral
coordinate-3 blow-up multiplies every Hessian entry containing one `3` index
by `X^e`, and the `(3,3)` entry by `X^(2e)`.  Both rigid chart points have
coordinate `3 = 0`, so spatial evaluation does not disturb these factors.
Consequently the cleared Schur `C` entry is divisible by `X^(2e)`.

The zero-Schur tail only removes `X^e`.  Therefore its constant kernel entry
vanishes.  If residual determinant order remains, the tail determinant-zero
identity forces the constant off-diagonal entry to vanish as well.  Since the
constant tail block is nonzero, its active coefficient is nonzero.  Thus the
residual rank-one pivot is canonically the left pivot.

This removes the arbitrary residual source-shear ambiguity: after a successful
first global stage, the second kernel is the other residual source coordinate
(`2` in the left rigid chart and `1` in the right rigid chart).
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A constant spatial point whose coordinate `3` is zero is fixed by the
coordinate-3 kernel point transformation. -/
theorem kernelBlowupSection_constantSection_three_of_zero
    (slope : ℕ)
    (point : Fin 4 -> K)
    (hpoint : point (3 : Fin 4) = 0) :
    kernelBlowupSection (3 : Fin 4) slope
        (polynomialConstantSection point) =
      polynomialConstantSection point := by
  funext i
  by_cases hi : i = (3 : Fin 4)
  · subst i
    simp [kernelBlowupSection, polynomialConstantSection, hpoint]
  · simp [kernelBlowupSection, polynomialConstantSection, hi]

/-- Entrywise evaluated Hessian scaling under coordinate-3 reinflation at a
point with third residual coordinate zero. -/
theorem evaluatedFamilyHessian_kernelInflate_three_entry
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 -> K)
    (hpoint : point (3 : Fin 4) = 0)
    (i j : Fin 4) :
    evaluatedFamilyHessian
        (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
        point i j =
      kernelInflateDerivativeCoefficient
          (K := K) (3 : Fin 4) slope i *
        kernelInflateDerivativeCoefficient
          (K := K) (3 : Fin 4) slope j *
        evaluatedFamilyHessian Q point i j := by
  change
    MvPolynomial.eval (polynomialConstantSection point)
        (HC4.Polynomial.hessian
          (kernelInflateHom (K := K) (3 : Fin 4) slope Q) i j) =
      kernelInflateDerivativeCoefficient
          (K := K) (3 : Fin 4) slope i *
        kernelInflateDerivativeCoefficient
          (K := K) (3 : Fin 4) slope j *
        MvPolynomial.eval (polynomialConstantSection point)
          (HC4.Polynomial.hessian Q i j)
  rw [hessian_kernelInflateHom_entry]
  simp only [map_mul, MvPolynomial.eval_C]
  rw [eval_kernelInflateHom]
  rw [kernelBlowupSection_constantSection_three_of_zero
    (K := K) slope point hpoint]

/-- If only the final source coordinate is scaled by a common factor `u`,
the cleared Schur kernel entry acquires exactly two copies of `u`.  Isolating
this tiny four-block identity avoids asking `simp` to normalize an entire
permuted Hessian expression. -/
theorem GeneralFourBlock.schurC_scale_lastCoordinate
    (H H' : GeneralFourBlock (Polynomial K))
    (u : Polynomial K)
    (ha : H'.a = H.a)
    (hb : H'.b = H.b)
    (hd : H'.d = H.d)
    (hq : H'.q = u * H.q)
    (hs : H'.s = u * H.s)
    (hz : H'.z = u * u * H.z) :
    H'.schurC = (u * u) * H.schurC := by
  simp only [GeneralFourBlock.schurC, GeneralFourBlock.activeDet]
  rw [ha, hb, hd, hq, hs, hz]
  ring

/-- Left rigid chart: the cleared kernel Schur entry acquires two copies of
the first kernel factor under reinflation. -/
theorem rigidExposureLeftFourBlock_schurC_kernelInflate_three
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureLeftFourBlock
        (kernelInflateHom (K := K) (3 : Fin 4) slope Q)).schurC =
      Polynomial.X ^ (2 * slope) *
        (rigidExposureLeftFourBlock Q).schurC := by
  have hpoint : rigidLeftChartPoint (K := K) (3 : Fin 4) = 0 := by
    simp [rigidLeftChartPoint, rankOnePacketTransversePoint]
  have hscale :
      (rigidExposureLeftFourBlock
          (kernelInflateHom (K := K) (3 : Fin 4) slope Q)).schurC =
        (Polynomial.X ^ slope * Polynomial.X ^ slope) *
          (rigidExposureLeftFourBlock Q).schurC := by
    apply GeneralFourBlock.schurC_scale_lastCoordinate
        (rigidExposureLeftFourBlock Q)
        (rigidExposureLeftFourBlock
          (kernelInflateHom (K := K) (3 : Fin 4) slope Q))
        (Polynomial.X ^ slope)
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            rigidLeftChartPoint 0 0 =
          evaluatedFamilyHessian Q rigidLeftChartPoint 0 0
      simpa [kernelInflateDerivativeCoefficient] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q rigidLeftChartPoint hpoint (0 : Fin 4) 0
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            rigidLeftChartPoint 0 1 =
          evaluatedFamilyHessian Q rigidLeftChartPoint 0 1
      simpa [kernelInflateDerivativeCoefficient] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q rigidLeftChartPoint hpoint (0 : Fin 4) 1
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            rigidLeftChartPoint 1 1 =
          evaluatedFamilyHessian Q rigidLeftChartPoint 1 1
      simpa [kernelInflateDerivativeCoefficient] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q rigidLeftChartPoint hpoint (1 : Fin 4) 1
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            rigidLeftChartPoint 0 3 =
          Polynomial.X ^ slope *
            evaluatedFamilyHessian Q rigidLeftChartPoint 0 3
      simpa [kernelInflateDerivativeCoefficient] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q rigidLeftChartPoint hpoint (0 : Fin 4) 3
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            rigidLeftChartPoint 1 3 =
          Polynomial.X ^ slope *
            evaluatedFamilyHessian Q rigidLeftChartPoint 1 3
      simpa [kernelInflateDerivativeCoefficient] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q rigidLeftChartPoint hpoint (1 : Fin 4) 3
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            rigidLeftChartPoint 3 3 =
          Polynomial.X ^ slope * Polynomial.X ^ slope *
            evaluatedFamilyHessian Q rigidLeftChartPoint 3 3
      simpa [kernelInflateDerivativeCoefficient] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q rigidLeftChartPoint hpoint (3 : Fin 4) 3
  rw [show 2 * slope = slope + slope by omega, pow_add]
  exact hscale

/-- Generic permutation-level form of the coordinate-3 Schur scaling law.

Keeping the permutation symbolic is important for elaboration: Lean never has
to reduce the concrete `Equiv.swap` defining the right rigid chart while
checking the six four-block projections.  The only hypotheses needed are that
the two active positions avoid source coordinate `3`, while the displayed
kernel position is source coordinate `3`. -/
theorem evaluatedFamilyHessianFourBlock_schurC_kernelInflate_three
    (rho : Equiv.Perm (Fin 4))
    (point : Fin 4 -> K)
    (hpoint : point (3 : Fin 4) = 0)
    (h0 : rho (0 : Fin 4) ≠ (3 : Fin 4))
    (h1 : rho (1 : Fin 4) ≠ (3 : Fin 4))
    (h3 : rho (3 : Fin 4) = (3 : Fin 4))
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (evaluatedFamilyHessianFourBlock rho
        (kernelInflateHom (K := K) (3 : Fin 4) slope Q) point).schurC =
      Polynomial.X ^ (2 * slope) *
        (evaluatedFamilyHessianFourBlock rho Q point).schurC := by
  have hscale :
      (evaluatedFamilyHessianFourBlock rho
          (kernelInflateHom (K := K) (3 : Fin 4) slope Q) point).schurC =
        (Polynomial.X ^ slope * Polynomial.X ^ slope) *
          (evaluatedFamilyHessianFourBlock rho Q point).schurC := by
    apply GeneralFourBlock.schurC_scale_lastCoordinate
        (evaluatedFamilyHessianFourBlock rho Q point)
        (evaluatedFamilyHessianFourBlock rho
          (kernelInflateHom (K := K) (3 : Fin 4) slope Q) point)
        (Polynomial.X ^ slope)
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            point (rho 0) (rho 0) =
          evaluatedFamilyHessian Q point (rho 0) (rho 0)
      simpa [kernelInflateDerivativeCoefficient, h0] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q point hpoint (rho 0) (rho 0)
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            point (rho 0) (rho 1) =
          evaluatedFamilyHessian Q point (rho 0) (rho 1)
      simpa [kernelInflateDerivativeCoefficient, h0, h1] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q point hpoint (rho 0) (rho 1)
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            point (rho 1) (rho 1) =
          evaluatedFamilyHessian Q point (rho 1) (rho 1)
      simpa [kernelInflateDerivativeCoefficient, h1] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q point hpoint (rho 1) (rho 1)
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            point (rho 0) (rho 3) =
          Polynomial.X ^ slope *
            evaluatedFamilyHessian Q point (rho 0) (rho 3)
      simpa [kernelInflateDerivativeCoefficient, h0, h3] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q point hpoint (rho 0) (rho 3)
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            point (rho 1) (rho 3) =
          Polynomial.X ^ slope *
            evaluatedFamilyHessian Q point (rho 1) (rho 3)
      simpa [kernelInflateDerivativeCoefficient, h1, h3] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q point hpoint (rho 1) (rho 3)
    · change
        evaluatedFamilyHessian
            (kernelInflateHom (K := K) (3 : Fin 4) slope Q)
            point (rho 3) (rho 3) =
          Polynomial.X ^ slope * Polynomial.X ^ slope *
            evaluatedFamilyHessian Q point (rho 3) (rho 3)
      simpa [kernelInflateDerivativeCoefficient, h3] using
        evaluatedFamilyHessian_kernelInflate_three_entry
          (K := K) slope Q point hpoint (rho 3) (rho 3)
  rw [show 2 * slope = slope + slope by omega, pow_add]
  exact hscale

/-- Divisibility of the cleared Schur kernel by `X^(2e)` forces its
coefficient at the smaller positive order `e` to vanish. -/
theorem coeff_first_eq_zero_of_schurC_twoFactor
    (e : ℕ)
    (he : 0 < e)
    (C T : Polynomial K)
    (hC : C = Polynomial.X ^ (2 * e) * T) :
    C.coeff e = 0 := by
  rw [hC, Polynomial.coeff_X_pow_mul']
  simp [Nat.not_le.mpr (by omega : e < 2 * e)]

/-- Once the first global coordinate-3 stage is integral, a recentered left
rigid block has zero constant kernel entry in its normalised Schur tail. -/
theorem recenteredLeft_tailKernel_coeff_zero_of_integralFirstStage
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingExactCollisionSourceData)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 D f.lossless.packet)
    (hpivot :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).LeftPivot)
    (hD : 3 ≤ D)
    (hint :
      CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.HasIntegralRigidClosingFirstKernelStage
        S.recenteredSourceData
        (S.recenteredLeftZeroSchurData hrigid hpivot hD)) :
    (S.recenteredLeftZeroSchurData hrigid hpivot hD).toClock.tailSeries.kernel.coeff 0 = 0 := by
  let B := S.recenteredLeftZeroSchurData hrigid hpivot hD
  let R := S.recenteredSourceData
  unfold CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.HasIntegralRigidClosingFirstKernelStage at hint
  dsimp only at hint
  rcases hint with ⟨hdiv, _hdef, _hcoll, _hspecial⟩
  let Qtilde := integralKernelBlowupFamily
    rigidClosingCommonKernel B.toClock.firstOrder R.family hdiv
  have hinflate :
      kernelInflateHom (K := K) rigidClosingCommonKernel
          B.toClock.firstOrder Qtilde = R.family := by
    exact kernelInflate_integralKernelBlowupFamily_eq
      rigidClosingCommonKernel B.toClock.firstOrder R.family hdiv
  have hscale :
      B.block.schurC =
        Polynomial.X ^ (2 * B.toClock.firstOrder) *
          (rigidExposureLeftFourBlock Qtilde).schurC := by
    change
      (rigidExposureLeftFourBlock R.family).schurC =
        Polynomial.X ^ (2 * B.toClock.firstOrder) *
          (rigidExposureLeftFourBlock Qtilde).schurC
    rw [← hinflate]
    exact rigidExposureLeftFourBlock_schurC_kernelInflate_three
      B.toClock.firstOrder Qtilde
  have hcoeff : B.block.schurC.coeff B.toClock.firstOrder = 0 :=
    coeff_first_eq_zero_of_schurC_twoFactor
      B.toClock.firstOrder B.toClock.firstOrder_pos
      B.block.schurC (rigidExposureLeftFourBlock Qtilde).schurC hscale
  have hclockCoeff :
      B.toClock.zeroSeries.series.kernel.coeff B.toClock.firstOrder = 0 := by
    change B.block.schurC.coeff B.toClock.firstOrder = 0
    exact hcoeff
  have htail :
      B.toClock.zeroSeries.series.kernel.coeff B.toClock.firstOrder =
        B.toClock.tailSeries.kernel.coeff 0 := by
    exact B.toClock.zeroSeries.kernel_coeff_first_eq_tail_zero
      B.toClock.hasPositiveEntryLayer
  change B.toClock.tailSeries.kernel.coeff 0 = 0
  exact htail.symm.trans hclockCoeff

/-- Right-chart analogue of the tail-kernel vanishing theorem. -/
theorem recenteredRight_tailKernel_coeff_zero_of_integralFirstStage
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingExactCollisionSourceData)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 D f.lossless.packet)
    (hpivot :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).RightAxisPivot)
    (hD : 3 ≤ D)
    (hint :
      CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.HasIntegralRigidClosingFirstKernelStage
        S.recenteredSourceData
        (S.recenteredRightZeroSchurData hrigid hpivot hD)) :
    (S.recenteredRightZeroSchurData hrigid hpivot hD).toClock.tailSeries.kernel.coeff 0 = 0 := by
  let B := S.recenteredRightZeroSchurData hrigid hpivot hD
  let R := S.recenteredSourceData
  unfold CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.HasIntegralRigidClosingFirstKernelStage at hint
  dsimp only at hint
  rcases hint with ⟨hdiv, _hdef, _hcoll, _hspecial⟩
  let Qtilde := integralKernelBlowupFamily
    rigidClosingCommonKernel B.toClock.firstOrder R.family hdiv
  have hinflate :
      kernelInflateHom (K := K) rigidClosingCommonKernel
          B.toClock.firstOrder Qtilde = R.family := by
    exact kernelInflate_integralKernelBlowupFamily_eq
      rigidClosingCommonKernel B.toClock.firstOrder R.family hdiv
  have hscale :
      B.block.schurC =
        Polynomial.X ^ (2 * B.toClock.firstOrder) *
          (rigidExposureRightFourBlock Qtilde).schurC := by
    change
      (rigidExposureRightFourBlock R.family).schurC =
        Polynomial.X ^ (2 * B.toClock.firstOrder) *
          (rigidExposureRightFourBlock Qtilde).schurC
    rw [← hinflate]
    have hpoint : rigidRightChartPoint (K := K) (3 : Fin 4) = 0 := by
      simp [rigidRightChartPoint, rankOnePacketTransversePoint]
    have h0 : rigidRightChartPerm (0 : Fin 4) ≠ (3 : Fin 4) := by simp
    have h1 : rigidRightChartPerm (1 : Fin 4) ≠ (3 : Fin 4) := by simp
    have h3 : rigidRightChartPerm (3 : Fin 4) = (3 : Fin 4) := by simp
    simpa only [rigidExposureRightFourBlock] using
      evaluatedFamilyHessianFourBlock_schurC_kernelInflate_three
        (K := K) rigidRightChartPerm rigidRightChartPoint hpoint h0 h1 h3
        B.toClock.firstOrder Qtilde
  have hcoeff : B.block.schurC.coeff B.toClock.firstOrder = 0 :=
    coeff_first_eq_zero_of_schurC_twoFactor
      B.toClock.firstOrder B.toClock.firstOrder_pos
      B.block.schurC (rigidExposureRightFourBlock Qtilde).schurC hscale
  have hclockCoeff :
      B.toClock.zeroSeries.series.kernel.coeff B.toClock.firstOrder = 0 := by
    change B.block.schurC.coeff B.toClock.firstOrder = 0
    exact hcoeff
  have htail :
      B.toClock.zeroSeries.series.kernel.coeff B.toClock.firstOrder =
        B.toClock.tailSeries.kernel.coeff 0 := by
    exact B.toClock.zeroSeries.kernel_coeff_first_eq_tail_zero
      B.toClock.hasPositiveEntryLayer
  change B.toClock.tailSeries.kernel.coeff 0 = 0
  exact htail.symm.trans hclockCoeff

/-- A positive-residual zero-Schur tail whose kernel constant vanishes must
use the left axis as its unique rank-one pivot. -/
theorem ExactZeroSchurClock.leftPivot_of_residual_pos_of_tailKernel_zero
    (E : ExactZeroSchurClock K)
    (hres : 0 < E.residualDefect)
    (hC : E.tailSeries.kernel.coeff 0 = 0) :
    E.tailSeries.LeftPivot := by
  have hdet := E.tail_constant_det_zero_of_residual_pos hres
  have hBB :
      E.tailSeries.offDiag.coeff 0 * E.tailSeries.offDiag.coeff 0 = 0 := by
    simpa [hC] using hdet.symm
  have hB : E.tailSeries.offDiag.coeff 0 = 0 := by
    rcases mul_eq_zero.mp hBB with hb | hb
    · exact hb
    · exact hb
  have hnonzero := E.tail_constantBlock_nonzero
  have hA : E.tailSeries.active.coeff 0 ≠ 0 := by
    rcases hnonzero with hA | hB' | hC'
    · exact hA
    · exact False.elim (hB' hB)
    · exact False.elim (hC' hC)
  exact ⟨hA, hdet⟩

end

end HC4.Valuation
