import HC4.Valuation.CertifiedFixedScaleRestartEpisodeProgress
import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoSaturated
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Degree-two saturated branch -> fixed-scale strict progress

The saturated degree-two endpoint is already geometric, but its target is
recorded on the denominator-clearing ramification scale `R` while its
exposed source is an ordinary adaptive state (scale `1`).

For the global fixed-scale episode order we must not compare those directly.
Instead we first *rebase* the exposed source by pure parameter ramification:

    source clock : R * Δ
    source scale : R.

This rebasing is zero-cost: it preserves the collision, degree cap, repair
state, source complexity and marked special point.

The saturated kernel blow-up then has target clock

    R * Δ - 2*q,

with `q > 0`.  The existing integral-kernel Hessian bound gives

    2*q ≤ R*Δ,

so the raw natural-number clock strictly decreases at one literal scale.

Thus the degree-two saturated output is a genuine recursive exit in every
certified fixed-scale episode order.  No quotient clock is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Zero-cost scale rebasing by parameter ramification -/

/-- Re-record an ordinary adaptive state on a positive ramification scale.

This is a pure parameter change, not progress.  The raw Hessian clock scales
from `Δ` to `R*Δ`, and the state is stored at literal scale `R`.
-/
noncomputable def AdaptiveGeometricRestartState.parameterRamifiedScaleAwareState
    (a : AdaptiveGeometricRestartState (K := K))
    (R : ℕ)
    (hR : 0 < R) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let Pram := parameterRamificationFamily (K := K) R a.family
  let bram := parameterRamificationSection (K := K) R a.movingSection

  have hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * a.defect) := by
    dsimp [Pram]
    exact
      parameterRamificationFamily_hasHessianDefect
        R a.defect a.family a.hessianDefect

  have hdegree :
      NonlinearDegreeBound a.degreeCap Pram := by
    dsimp [Pram]
    exact
      nonlinearDegreeBound_parameterRamification
        a.degreeCap R a.family a.nonlinearDegreeBound

  have hcollisionRaw :=
    polynomialFamilyExactGradientCollision_parameterRamification
      R a.family
      (zeroPolynomialSection (K := K))
      a.movingSection a.exactCollision

  have hzero :
      parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K)) =
        zeroPolynomialSection (K := K) := by
    funext i
    simp [zeroPolynomialSection, parameterRamificationSection,
      parameterRamificationHom]

  have hcollision :
      HasPolynomialFamilyExactGradientCollision
        Pram (zeroPolynomialSection (K := K)) bram := by
    rw [hzero] at hcollisionRaw
    simpa [Pram, bram] using hcollisionRaw

  have hspecial :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bram]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hR a.movingSection]
    exact a.sectionSpecial

  exact
    {
      rawDefect := R * a.defect
      scale := R
      scale_pos := hR
      degreeCap := a.degreeCap
      sourceComplexity := a.sourceComplexity
      repair := a.repair
      family := Pram
      movingSection := bram
      hessianDefect := hdef
      nonlinearDegreeBound := hdegree
      exactCollision := hcollision
      sectionSpecial := hspecial
    }

@[simp]
theorem AdaptiveGeometricRestartState.parameterRamifiedScaleAwareState_rawDefect
    (a : AdaptiveGeometricRestartState (K := K))
    (R : ℕ)
    (hR : 0 < R) :
    (a.parameterRamifiedScaleAwareState R hR).rawDefect =
      R * a.defect := rfl

@[simp]
theorem AdaptiveGeometricRestartState.parameterRamifiedScaleAwareState_scale
    (a : AdaptiveGeometricRestartState (K := K))
    (R : ℕ)
    (hR : 0 < R) :
    (a.parameterRamifiedScaleAwareState R hR).scale = R := rfl

/-! ## Saturated D=2 output pays strict raw-defect progress -/

/-- The actual saturated degree-two endpoint is strict fixed-scale progress
from the purely ramified version of its exposed source.

The packet `P` is used only to recover the exact quadratic balanced-face
support, which proves coordinate `3` is absent on the exposed special fibre.
That gives positivity of the saturated first-contact slope. -/
theorem AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint.exists_certifiedFixedScaleStrictSuccessor
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint (K := K) s W) :
    let a₂ := S.exposure.toAdaptiveState S.canonicalSpecial
    let hactive :=
      exists_kernelDependentSupport_of_hessianDefect
        (K := K) (3 : Fin 4) a₂.family a₂.defect a₂.hessianDefect
    let R :=
      kernelSlopeDenominatorClearingRamification
        (3 : Fin 4) a₂.family
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target
        (a₂.parameterRamifiedScaleAwareState R
          (kernelSlopeDenominatorClearingRamification_pos
            (3 : Fin 4) a₂.family)) ∧
      (∃ d ∈ (polynomialFamilySpecialFiber target.family).support,
        0 < d (3 : Fin 4)) := by
  dsimp only

  let a := W.original.aligned.toAdaptiveState s
  let a₂ := S.exposure.toAdaptiveState S.canonicalSpecial
  let T := W.balancedSubface s
  let F := a.normalizedSpecialFiber

  have hspecial :
      polynomialFamilySpecialFiber a₂.family =
        smithSubfacePolynomial (1 : Fin 4) 2 3 T F := by
    simpa [a₂, T, F, a,
      AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface] using
      S.exposure.toAdaptiveState_specialFiber S.canonicalSpecial

  have hquad :
      ∀ e ∈ T,
        (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
        (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
        (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
    intro e he
    exact P.quadratic e (by simpa [T] using he)

  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber a₂.family).support,
        d (3 : Fin 4) = 0 := by
    rw [hspecial]
    exact quadraticSmithSubface_free_three T F hquad

  let hactive :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) (3 : Fin 4) a₂.family a₂.defect a₂.hessianDefect
  let R :=
    kernelSlopeDenominatorClearingRamification
      (3 : Fin 4) a₂.family
  let q :=
    saturatedKernelSlope (3 : Fin 4) a₂.family hactive

  have hRpos : 0 < R := by
    dsimp [R]
    exact
      kernelSlopeDenominatorClearingRamification_pos
        (3 : Fin 4) a₂.family

  have hqpos : 0 < q := by
    dsimp [q]
    exact
      saturatedKernelSlope_pos
        (3 : Fin 4) a₂.family hactive hfree

  let Pram := parameterRamificationFamily (K := K) R a₂.family
  let hdiv :=
    saturatedKernelSlope_divisibility_afterRamification
      (K := K) (3 : Fin 4) a₂.family hactive

  have hdefRam :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * a₂.defect) := by
    dsimp [Pram, R]
    exact
      parameterRamificationFamily_hasHessianDefect
        (kernelSlopeDenominatorClearingRamification
          (3 : Fin 4) a₂.family)
        a₂.defect a₂.family a₂.hessianDefect

  have hcost :
      2 * q ≤ R * a₂.defect := by
    dsimp [q, R, Pram, hdiv] at *
    exact
      two_mul_slope_le_of_integralKernelBlowup
        (K := K)
        (3 : Fin 4)
        (saturatedKernelSlope (3 : Fin 4) a₂.family hactive)
        (kernelSlopeDenominatorClearingRamification
          (3 : Fin 4) a₂.family * a₂.defect)
        (parameterRamificationFamily (K := K)
          (kernelSlopeDenominatorClearingRamification
            (3 : Fin 4) a₂.family) a₂.family)
        (saturatedKernelSlope_divisibility_afterRamification
          (K := K) (3 : Fin 4) a₂.family hactive)
        hdefRam

  have hclock :
      R * a₂.defect - 2 * q < R * a₂.defect := by
    omega

  rcases S.stage with ⟨target, htargetRaw, htargetScale, _hqstage, hactiveTarget⟩

  refine ⟨target, ?_, hactiveTarget⟩

  have hsame :
      SameEpisodeScale target
        (a₂.parameterRamifiedScaleAwareState R hRpos) := by
    unfold SameEpisodeScale
    rw [htargetScale]
    rfl

  apply
    certifiedFixedScaleEpisodeProgress_of_rawDefect_lt
      (K := K) RR hsame
  rw [htargetRaw]
  exact hclock

end

end HC4.Valuation
