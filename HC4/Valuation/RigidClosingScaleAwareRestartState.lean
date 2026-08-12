import HC4.Valuation.RigidClosingFixedScaleProgress
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# Scale-aware geometric re-entry for rigid closing restarts

A rigid closing restart is already a genuine polynomial-family kernel
blow-up.  The remaining global interface is representational: package the
pre- and post-blow-up geometries as `ScaleAwareAdaptiveGeometricRestartState`
objects on the *same* aligned-Smith parameter scale, and then invoke the
fixed-scale raw-clock progress theorem.

No full-family homogeneity is assumed here.  The nonlinear degree ceiling is
an explicit hypothesis and is transported by the generic integral-kernel
blow-up preservation theorem.

For a rigid source `S` and a strict restart witness of slope `q`, the states
have clocks

    source : R * f.defect
    target : R * f.defect - 2*q,

where `R = alignedSmithRamificationIndex`, and both have literal scale `R`.
Thus the positive kernel spend is a genuine strict recursive exit in the
certified fixed-scale episode order.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The rigid recentered source, viewed as an actual scale-aware adaptive
state on the aligned-Smith parameter scale.

The degree ceiling and the two finite bookkeeping coordinates are supplied
by the outer adaptive episode; the rigid source itself already carries the
family, exact Hessian clock, exact zero-left collision and canonical right
special point.
-/
noncomputable def CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.scaleAwareSourceState
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData)
    (degreeCap sourceComplexity : ℕ)
    (repair : RepairState)
    (hdegree : NonlinearDegreeBound degreeCap S.family) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) :=
  {
    rawDefect := alignedSmithRamificationIndex * f.defect
    scale := alignedSmithRamificationIndex
    scale_pos := alignedSmithRamificationIndex_pos
    degreeCap := degreeCap
    sourceComplexity := sourceComplexity
    repair := repair
    family := S.family
    movingSection := S.rightSection
    hessianDefect := S.hessianDefect
    nonlinearDegreeBound := hdegree
    exactCollision := S.exactCollision
    sectionSpecial := S.rightSpecial
  }

/-- The transformed right section of one concrete rigid kernel restart. -/
noncomputable def CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartRightSection
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData)
    (q : ℕ) :
    Fin 4 → Polynomial K :=
  kernelBlowupSection rigidClosingCommonKernel q S.rightSection

/-- The transformed polynomial family of one concrete rigid kernel restart. -/
noncomputable def CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartFamily
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData)
    (q : ℕ)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel q S.family) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  integralKernelBlowupFamily
    rigidClosingCommonKernel q S.family hdiv

/-- Kernel blow-up preserves the canonical right special point `e₀` because
the rigid common kernel is coordinate `3`, while the marked nonzero
coordinate is `0`. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartRightSpecial
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData)
    (q : ℕ)
    (hq : 0 < q) :
    polynomialSectionSpecialPoint
        (S.kernelRestartRightSection q) =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  funext i
  by_cases hi : i = rigidClosingCommonKernel
  · subst i
    dsimp [CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartRightSection]
    rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
      rigidClosingCommonKernel hq S.rightSection]
    simp [rigidClosingCommonKernel, coordinateAxisPoint]
  · dsimp [CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartRightSection]
    rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
      rigidClosingCommonKernel q S.rightSection hi]
    exact congrFun S.rightSpecial i

/-- Construct the actual post-kernel-blow-up scale-aware state.

Both source and target use the same fixed aligned-Smith scale.  The repair
and source-complexity fields are unchanged; the recursive payment is entirely
the strict raw Hessian-clock drop.
-/
noncomputable def CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.scaleAwareKernelRestartTarget
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData)
    (degreeCap sourceComplexity : ℕ)
    (repair : RepairState)
    (q : ℕ)
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        rigidClosingCommonKernel q S.family)
    (hq : 0 < q)
    (hdegree : NonlinearDegreeBound degreeCap S.family) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let Pnext :=
    CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartFamily
      S q hdiv
  let bnext :=
    CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartRightSection
      S q

  have hdefNext :
      HasPolynomialFamilyHessianDefect
        (K := K) Pnext
        (alignedSmithRamificationIndex * f.defect - 2 * q) := by
    dsimp [Pnext,
      CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartFamily]
    exact
      integralKernelBlowup_hasHessianDefect_sub
        rigidClosingCommonKernel q
        (alignedSmithRamificationIndex * f.defect)
        S.family hdiv S.hessianDefect

  have hdegreeNext :
      NonlinearDegreeBound degreeCap Pnext := by
    dsimp [Pnext,
      CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartFamily]
    exact
      nonlinearDegreeBound_integralKernelBlowup
        degreeCap q rigidClosingCommonKernel
        S.family hdegree hdiv

  have hcollRaw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      rigidClosingCommonKernel q S.family hdiv
      (zeroPolynomialSection (K := K))
      S.rightSection S.exactCollision

  have hcollNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (zeroPolynomialSection (K := K)) bnext := by
    have hzero :
        kernelBlowupSection rigidClosingCommonKernel q
            (zeroPolynomialSection (K := K)) =
          zeroPolynomialSection (K := K) := by
      funext i
      simp [kernelBlowupSection, zeroPolynomialSection]
    rw [hzero] at hcollRaw
    simpa [Pnext, bnext,
      CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartFamily,
      CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartRightSection]
      using hcollRaw

  exact
    {
      rawDefect := alignedSmithRamificationIndex * f.defect - 2 * q
      scale := alignedSmithRamificationIndex
      scale_pos := alignedSmithRamificationIndex_pos
      degreeCap := degreeCap
      sourceComplexity := sourceComplexity
      repair := repair
      family := Pnext
      movingSection := bnext
      hessianDefect := hdefNext
      nonlinearDegreeBound := hdegreeNext
      exactCollision := hcollNext
      sectionSpecial :=
        CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.kernelRestartRightSpecial
          S q hq
    }

/-- **Rigid closing gives an actual strict scale-aware geometric successor.**

This is the representation bridge missing from the legacy rigid restart
certificate.  It constructs the genuine target family/section and proves
strict progress in the new well-founded episode order.
-/
theorem HasRigidClosingStrictKernelRestart.exists_scaleAwareStrictSuccessor
    (R : RepairRanking)
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (S : f.RigidClosingRecenteredSourceData)
    (h : S.HasRigidClosingStrictKernelRestart)
    (degreeCap sourceComplexity : ℕ)
    (repair : RepairState)
    (hdegree : NonlinearDegreeBound degreeCap S.family) :
    ∃ q : ℕ,
      ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        0 < q ∧
        target.rawDefect =
          alignedSmithRamificationIndex * f.defect - 2 * q ∧
        target.scale = alignedSmithRamificationIndex ∧
        CertifiedFixedScaleEpisodeProgress R target
          (CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.scaleAwareSourceState
            S degreeCap sourceComplexity repair hdegree) := by
  rcases h with ⟨q, hdiv, hq, hcert⟩

  let source :=
    CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.scaleAwareSourceState
      S degreeCap sourceComplexity repair hdegree
  let target :=
    CanonicalSmithDepartureFrontier.RigidClosingRecenteredSourceData.scaleAwareKernelRestartTarget
      S degreeCap sourceComplexity repair q hdiv hq hdegree

  have hdrop := hcert.positiveDefectDrop
  rcases hdrop with ⟨_hqdrop, hle, _hdefect⟩

  have hclock :
      alignedSmithRamificationIndex * f.defect - 2 * q <
        alignedSmithRamificationIndex * f.defect := by
    have hcost : 0 < 2 * q := by omega
    have hsourcePos :
        0 < alignedSmithRamificationIndex * f.defect := by
      by_contra hnot
      have hzero :
          alignedSmithRamificationIndex * f.defect = 0 :=
        Nat.eq_zero_of_not_pos hnot
      have hbad : 2 * q ≤ 0 := by
        simpa [hzero] using hle
      omega
    omega

  refine ⟨q, target, hq, rfl, rfl, ?_⟩
  exact
    certifiedFixedScaleEpisodeProgress_of_rigidClock
      (K := K) R q
      (source := source) (target := target)
      rfl rfl rfl rfl hclock

end

end HC4.Valuation
