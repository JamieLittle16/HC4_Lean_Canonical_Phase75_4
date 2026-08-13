import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoFixedScaleProgress
import HC4.Valuation.IntegralKernelSlopeExtraction
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Positive integral kernel slope -> certified adaptive fixed-scale progress

The older rigid-closing restart stack proves this construction only through a
legacy `CanonicalSmithDepartureFrontier`.  The actual kernel blow-up argument
is independent of that wrapper.

This file packages the reusable adaptive statement directly.  For any honest
`AdaptiveGeometricRestartState`, any positive integral source-kernel slope in
a transverse coordinate gives a genuine scale-one successor with raw Hessian
clock

    Delta - 2*q,

with the same degree cap, repair state, source complexity and marked collision.
Consequently the target is strict `CertifiedFixedScaleEpisodeProgress`.

We also package the complementary maximal-slope-zero obstruction.  This is the
right common interface for the remaining aligned-Smith blocker branches: once
all immediately available positive kernel slopes have been consumed, every
survivor carries an explicit source-level zero-slope certificate instead of an
opaque closing label.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Actual scale-one target of one positive integral kernel blow-up on an
adaptive source state. -/
noncomputable def AdaptiveGeometricRestartState.integralKernelScaleOneTarget
    (a : AdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (q : ℕ)
    (hdiv : HasIntegralKernelCoefficientDivisibility kernel q a.family)
    (hq : 0 < q)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let Pnext := integralKernelBlowupFamily kernel q a.family hdiv
  let bnext := kernelBlowupSection kernel q a.movingSection

  have hdefNext :
      HasPolynomialFamilyHessianDefect
        (K := K) Pnext (a.defect - 2 * q) := by
    dsimp [Pnext]
    exact
      integralKernelBlowup_hasHessianDefect_sub
        kernel q a.defect a.family hdiv a.hessianDefect

  have hdegreeNext : NonlinearDegreeBound a.degreeCap Pnext := by
    dsimp [Pnext]
    exact
      nonlinearDegreeBound_integralKernelBlowup
        a.degreeCap q kernel a.family a.nonlinearDegreeBound hdiv

  have hcollRaw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q a.family hdiv
      (zeroPolynomialSection (K := K)) a.movingSection a.exactCollision

  have hzero :
      kernelBlowupSection kernel q (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) :=
    kernelBlowupSection_zeroPolynomialSection kernel q

  have hcollNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (zeroPolynomialSection (K := K)) bnext := by
    rw [hzero] at hcollRaw
    simpa [Pnext, bnext] using hcollRaw

  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bnext]
    exact
      polynomialSectionSpecialPoint_kernelBlowupSection_axisZero_of_kernel_ne_zero
        kernel hq hkernel a.movingSection a.sectionSpecial

  exact
    {
      rawDefect := a.defect - 2 * q
      scale := 1
      scale_pos := by omega
      degreeCap := a.degreeCap
      sourceComplexity := a.sourceComplexity
      repair := a.repair
      family := Pnext
      movingSection := bnext
      hessianDefect := hdefNext
      nonlinearDegreeBound := hdegreeNext
      exactCollision := hcollNext
      sectionSpecial := hspecialNext
    }

/-- A positive integral transverse kernel slope is a genuine strict recursive
exit at literal scale one. -/
theorem AdaptiveGeometricRestartState.exists_certifiedFixedScaleStrictSuccessor_of_positiveIntegralKernelSlope
    (RR : RepairRanking)
    (a : AdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (q : ℕ)
    (hq : 0 < q)
    (hdiv : HasIntegralKernelCoefficientDivisibility kernel q a.family) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target a.toScaleAware := by
  let target := a.integralKernelScaleOneTarget kernel q hdiv hq hkernel

  have hcost : 2 * q ≤ a.defect :=
    two_mul_slope_le_of_integralKernelBlowup
      kernel q a.defect a.family hdiv a.hessianDefect

  have hclock : a.defect - 2 * q < a.defect := by
    omega

  have hsame : SameEpisodeScale target a.toScaleAware := by
    rfl
  have htargetRaw : target.rawDefect = a.defect - 2 * q := by
    rfl
  have hsourceRaw : a.toScaleAware.rawDefect = a.defect := by
    rfl
  refine ⟨target, ?_⟩
  apply certifiedFixedScaleEpisodeProgress_of_rawDefect_lt RR hsame
  rw [htargetRaw, hsourceRaw]
  exact hclock

/-- Explicit source-level obstruction left after the maximal integral slope in
one transverse coordinate is zero. -/
structure AdaptiveKernelZeroSlopeObstruction
    (a : AdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4) : Prop where
  active : IsActiveKernelCoordinate kernel a.family
  maximal_eq_zero :
    maximalIntegralKernelSlope kernel a.family active = 0

/-- The zero-slope certificate really means that no positive integral source
kernel blow-up exists in that coordinate. -/
theorem AdaptiveKernelZeroSlopeObstruction.no_positive_integral_slope
    {a : AdaptiveGeometricRestartState (K := K)}
    {kernel : Fin 4}
    (Z : AdaptiveKernelZeroSlopeObstruction a kernel) :
    ¬ ∃ q : ℕ,
      0 < q ∧ HasIntegralKernelCoefficientDivisibility kernel q a.family := by
  exact
    no_positive_admissible_of_maximalIntegralKernelSlope_eq_zero
      kernel a.family Z.active Z.maximal_eq_zero

/-- **Universal adaptive kernel normalisation.**

For any transverse coordinate, an adaptive state either admits immediate
certified fixed-scale progress by its maximal positive integral slope, or it
is already in the explicit maximal-slope-zero source geometry. -/
theorem AdaptiveGeometricRestartState.certifiedStrict_or_zeroSlope
    (RR : RepairRanking)
    (a : AdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4)) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target a.toScaleAware) ∨
      AdaptiveKernelZeroSlopeObstruction a kernel := by
  let hactive : IsActiveKernelCoordinate kernel a.family :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel a.family a.defect a.hessianDefect

  rcases maximalIntegralKernelSlope_zero_or_positive
      kernel a.family hactive with hzero | hpos
  · exact Or.inr ⟨hactive, hzero.1⟩
  · left
    exact
      a.exists_certifiedFixedScaleStrictSuccessor_of_positiveIntegralKernelSlope
        RR kernel hkernel
        (maximalIntegralKernelSlope kernel a.family hactive)
        hpos.1 hpos.2

end

end HC4.Valuation
