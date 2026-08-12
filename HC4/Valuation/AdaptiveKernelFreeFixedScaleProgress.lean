import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoFixedScaleProgress
import HC4.Valuation.AdaptiveAlignedSmithStateBridge
import Mathlib.Tactic

/-!
# Kernel-free special fibre -> certified fixed-scale strict progress

The saturated kernel restart used in the degree-two branch is not intrinsically
quadratic.  The degree-two packet was used only to prove that coordinate `3`
is absent from the exposed special fibre.

This file extracts the generic statement.  For any adaptive state whose
special fibre is free of coordinate `3`, the pure Hessian clock makes
coordinate `3` active in the source family, the saturated first kernel slope
is positive, and the existing denominator-cleared integral-kernel blow-up
strictly decreases the raw defect at one literal scale.

This is the exact destination needed by a genuinely pure-longitudinal blocker:
once transverse-freeness is established, no further local geometry or JC2
input is required.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- **Generic kernel-free fixed-scale progress.**

The old degree-two proof only used its quadratic packet to establish `hfree`.
Once coordinate `3` is absent from the special fibre, the existing saturated
kernel machinery produces a positive first-contact slope and therefore a
strict raw-defect drop after rebasing the source to the denominator-clearing
ramification scale.
-/
theorem AdaptiveGeometricRestartState.exists_certifiedFixedScaleStrictSuccessor_of_specialFiber_free_three
    (RR : RepairRanking)
    (a : AdaptiveGeometricRestartState (K := K))
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber a.family).support,
        d (3 : Fin 4) = 0) :
    let hactive :=
      exists_kernelDependentSupport_of_hessianDefect
        (K := K) (3 : Fin 4) a.family a.defect a.hessianDefect
    let R :=
      kernelSlopeDenominatorClearingRamification
        (3 : Fin 4) a.family
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target
        (a.parameterRamifiedScaleAwareState R
          (kernelSlopeDenominatorClearingRamification_pos
            (3 : Fin 4) a.family)) ∧
      (∃ d ∈ (polynomialFamilySpecialFiber target.family).support,
        0 < d (3 : Fin 4)) := by
  dsimp only

  let hactive :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) (3 : Fin 4) a.family a.defect a.hessianDefect
  let R :=
    kernelSlopeDenominatorClearingRamification
      (3 : Fin 4) a.family
  let q :=
    saturatedKernelSlope (3 : Fin 4) a.family hactive

  have hRpos : 0 < R := by
    dsimp [R]
    exact
      kernelSlopeDenominatorClearingRamification_pos
        (3 : Fin 4) a.family

  have hqpos : 0 < q := by
    dsimp [q]
    exact
      saturatedKernelSlope_pos
        (3 : Fin 4) a.family hactive hfree

  let Pram := parameterRamificationFamily (K := K) R a.family
  let hdiv :=
    saturatedKernelSlope_divisibility_afterRamification
      (K := K) (3 : Fin 4) a.family hactive

  have hdefRam :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * a.defect) := by
    dsimp [Pram, R]
    exact
      parameterRamificationFamily_hasHessianDefect
        (kernelSlopeDenominatorClearingRamification
          (3 : Fin 4) a.family)
        a.defect a.family a.hessianDefect

  have hcost :
      2 * q ≤ R * a.defect := by
    dsimp [q, R, Pram, hdiv] at *
    exact
      two_mul_slope_le_of_integralKernelBlowup
        (K := K)
        (3 : Fin 4)
        (saturatedKernelSlope (3 : Fin 4) a.family hactive)
        (kernelSlopeDenominatorClearingRamification
          (3 : Fin 4) a.family * a.defect)
        (parameterRamificationFamily (K := K)
          (kernelSlopeDenominatorClearingRamification
            (3 : Fin 4) a.family) a.family)
        (saturatedKernelSlope_divisibility_afterRamification
          (K := K) (3 : Fin 4) a.family hactive)
        hdefRam

  have hclock :
      R * a.defect - 2 * q < R * a.defect := by
    omega

  rcases a.degreeTwoSaturatedKernelStage hactive hfree with
    ⟨target, htargetRaw, htargetScale, _hqstage, hactiveTarget⟩

  refine ⟨target, ?_, hactiveTarget⟩

  have hsame :
      SameEpisodeScale target
        (a.parameterRamifiedScaleAwareState R hRpos) := by
    unfold SameEpisodeScale
    rw [htargetScale]
    rfl

  apply
    certifiedFixedScaleEpisodeProgress_of_rawDefect_lt
      (K := K) RR hsame
  rw [htargetRaw]
  exact hclock

/-- Blocker-facing adapter.  If the aligned endpoint's raw special fibre is
already free of coordinate `3`, then the endpoint is a certified strict
fixed-scale restart immediately.  This theorem is intentionally independent
of the blocker pattern; the remaining pure-longitudinal work is only to
manufacture the freeness certificate. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.exists_certifiedFixedScaleStrictSuccessor_of_rawSpecialFiber_free_three
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (hfree :
      ∀ d ∈ B.aligned.endpoint.rawSpecialFiber.support,
        d (3 : Fin 4) = 0) :
    let a := B.aligned.toAdaptiveState s
    let hactive :=
      exists_kernelDependentSupport_of_hessianDefect
        (K := K) (3 : Fin 4) a.family a.defect a.hessianDefect
    let R :=
      kernelSlopeDenominatorClearingRamification
        (3 : Fin 4) a.family
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR target
        (a.parameterRamifiedScaleAwareState R
          (kernelSlopeDenominatorClearingRamification_pos
            (3 : Fin 4) a.family)) ∧
      (∃ d ∈ (polynomialFamilySpecialFiber target.family).support,
        0 < d (3 : Fin 4)) := by
  dsimp only
  let a := B.aligned.toAdaptiveState s
  apply a.exists_certifiedFixedScaleStrictSuccessor_of_specialFiber_free_three RR
  intro d hd
  apply hfree d
  simpa [a, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber] using hd

end

end HC4.Valuation
