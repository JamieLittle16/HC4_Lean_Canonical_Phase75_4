import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFreeFirstContact
import Mathlib.Tactic

/-!
# A18.4.44: retain the actual saturated first-contact state

A18.4.43 stops consuming a kernel-free opening as anonymous rational descent.
For the nonlinear branch the final rank ladder needs one further piece of
provenance: the nonzero diagonal Hessian entry must live on an actual
scale-aware continuation state, not merely on an isolated special-fibre
polynomial.

This file packages the standard denominator-cleared saturated opening itself
as a `ScaleAwareAdaptiveGeometricRestartState`.  It is the same family and
section historically used to construct the ramified-spend certificate, but no
recursive progress is claimed for the ramified move.  The A18.4.39 nonlinear
witness is then transported literally to the special fibre of this retained
state.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The actual state obtained by denominator clearing followed by the
canonical saturated kernel blow-up.

The construction is deliberately presentation-valued.  Its scale is the true
absolute ramified scale and its repair/source coordinates are unchanged. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hq : 0 < saturatedKernelSlope kernel s.family hactive) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  let R := kernelSlopeDenominatorClearingRamification kernel s.family
  let q := saturatedKernelSlope kernel s.family hactive
  let Pram := parameterRamificationFamily (K := K) R s.family
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel s.family hactive
  let Pnext := integralKernelBlowupFamily kernel q Pram hdiv
  let bram := parameterRamificationSection (K := K) R s.movingSection
  let bnext := kernelBlowupSection kernel q bram

  have hRpos : 0 < R := by
    dsimp [R]
    exact kernelSlopeDenominatorClearingRamification_pos kernel s.family

  have hdefRam :
      HasPolynomialFamilyHessianDefect (K := K) Pram (R * s.rawDefect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R s.rawDefect s.family s.hessianDefect
  have hdefNext :
      HasPolynomialFamilyHessianDefect
        (K := K) Pnext (R * s.rawDefect - 2 * q) := by
    dsimp [Pnext]
    exact integralKernelBlowup_hasHessianDefect_sub
      kernel q (R * s.rawDefect) Pram hdiv hdefRam

  have hdegreeRam : NonlinearDegreeBound s.degreeCap Pram := by
    dsimp [Pram]
    exact nonlinearDegreeBound_parameterRamification
      s.degreeCap R s.family s.nonlinearDegreeBound
  have hdegreeNext : NonlinearDegreeBound s.degreeCap Pnext := by
    dsimp [Pnext]
    exact nonlinearDegreeBound_integralKernelBlowup
      s.degreeCap q kernel Pram hdegreeRam hdiv

  have hcollisionRam :
      HasPolynomialFamilyExactGradientCollision
        Pram
        (parameterRamificationSection (K := K) R
          (zeroPolynomialSection (K := K))) bram :=
    polynomialFamilyExactGradientCollision_parameterRamification
      R s.family (zeroPolynomialSection (K := K)) s.movingSection
      s.exactCollision
  have hcollisionNextRaw :=
    polynomialFamilyExactGradientCollision_integralKernelBlowup
      kernel q Pram hdiv
      (parameterRamificationSection (K := K) R
        (zeroPolynomialSection (K := K))) bram hcollisionRam
  have hzeroSection :
      kernelBlowupSection kernel q
          (parameterRamificationSection (K := K) R
            (zeroPolynomialSection (K := K))) =
        zeroPolynomialSection (K := K) := by
    funext i
    simp [kernelBlowupSection, parameterRamificationSection,
      parameterRamificationHom, zeroPolynomialSection]
  have hcollisionNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (zeroPolynomialSection (K := K)) bnext := by
    rw [hzeroSection] at hcollisionNextRaw
    simpa [Pnext, bnext] using hcollisionNextRaw

  have hspecialRam :
      polynomialSectionSpecialPoint bram =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bram]
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      R hRpos s.movingSection]
    exact s.sectionSpecial
  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    by_cases hi : i = kernel
    · subst i
      rw [polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hq bram]
      simp [coordinateAxisPoint, hkernel]
    · rw [polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel q bram hi]
      exact congrFun hspecialRam i

  exact {
    rawDefect := R * s.rawDefect - 2 * q
    scale := R * s.scale
    scale_pos := Nat.mul_pos hRpos s.scale_pos
    degreeCap := s.degreeCap
    sourceComplexity := s.sourceComplexity
    repair := s.repair
    family := Pnext
    movingSection := bnext
    hessianDefect := hdefNext
    nonlinearDegreeBound := hdegreeNext
    exactCollision := hcollisionNext
    sectionSpecial := hspecialNext
  }

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState_scale
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hq : 0 < saturatedKernelSlope kernel s.family hactive) :
    (s.saturatedKernelOpeningState kernel hkernel hactive hq).scale =
      kernelSlopeDenominatorClearingRamification kernel s.family * s.scale := by
  rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hq : 0 < saturatedKernelSlope kernel s.family hactive) :
    (s.saturatedKernelOpeningState kernel hkernel hactive hq).repair = s.repair := by
  rfl

@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState_sourceComplexity
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hq : 0 < saturatedKernelSlope kernel s.family hactive) :
    (s.saturatedKernelOpeningState kernel hkernel hactive hq).sourceComplexity =
      s.sourceComplexity := by
  rfl

/-- **State-valued first-contact dichotomy.**

The nonlinear alternative now names the actual scale-aware saturated-opening
state on whose special fibre the diagonal Hessian becomes nonzero. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeFirstContact_unramified_or_nonlinearOpening
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    let hq : 0 < saturatedKernelSlope kernel s.family hactive :=
      saturatedKernelSlope_pos kernel s.family hactive hfree
    let opening := s.saturatedKernelOpeningState kernel hkernel hactive hq
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      ∃ d ∈ (polynomialFamilySpecialFiber opening.family).support,
        2 ≤ d kernel ∧
        MvPolynomial.pderiv kernel
          (MvPolynomial.pderiv kernel
            (polynomialFamilySpecialFiber opening.family)) ≠ 0 := by
  let hq : 0 < saturatedKernelSlope kernel s.family hactive :=
    saturatedKernelSlope_pos kernel s.family hactive hfree
  let opening := s.saturatedKernelOpeningState kernel hkernel hactive hq
  cases s.kernelFreeFirstContact_unramified_or_nonlinearHessian
      RR kernel hkernel hactive hfree with
  | inl hprogress =>
      exact Or.inl hprogress
  | inr hnonlinear =>
      right
      dsimp only at hnonlinear ⊢
      simpa [opening, hq,
        ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState] using
        hnonlinear

end

end HC4.Valuation
