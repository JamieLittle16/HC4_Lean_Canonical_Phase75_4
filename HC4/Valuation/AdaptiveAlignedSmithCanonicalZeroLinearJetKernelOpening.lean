import HC4.Valuation.AdaptiveAlignedSmithCanonicalLinearFirstContactMixedHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactState
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination
import Mathlib.Tactic

/-!
# A18.4.65: zero-linear-jet saturated opening is directly rank two

A18.4.64 shows that a positive kernel first-contact monomial creates a nonzero
Hessian entry as soon as source-linear monomials are absent: exponent at least
two gives a diagonal entry, while exponent one forces a mixed entry with a
second source coordinate.

For the canonical HC4 families we can check the needed linear-jet condition
*before* denominator clearing.  Vanishing of the full family gradient at the
source origin kills every source-linear coefficient over `K[tau]`.  The exact
coefficient formula for the saturated special fibre then says that the same
linear exponent cannot reappear at first contact.

Thus a kernel-free saturated opening of such a family has no unramified
"linear" escape at all.  The actual post-opening family always contains
Hessian geometry involving the newly opened transverse coordinate, and this
geometry licenses the rank-one to rank-two promotion on that actual family.
No rational or presented-scale recursive edge remains.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Vanishing of the family source gradient at the literal source origin kills
its full `K[tau]` source-linear coefficients, not merely their special-fibre
constant terms. -/
theorem family_linearCoeff_zero_of_gradientAtZero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i P) = 0)
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1) P = 0 := by
  have hi := hgrad i
  rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] at hi
  rw [coeff_pderiv_mixedDegree
    (K := Polynomial K) i P (0 : Fin 4 →₀ ℕ)] at hi
  simpa using hi

/-- A source-linear exponent which is absent from the incoming full family is
also absent from the saturated first-contact special fibre.  This is an
immediate consequence of the exact saturated coefficient formula. -/
theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState_specialFiber_linearCoeff_zero
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hq : 0 < saturatedKernelSlope kernel s.family hactive)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i s.family) = 0)
    (i : Fin 4) :
    MvPolynomial.coeff (Finsupp.single i 1)
        (polynomialFamilySpecialFiber
          (s.saturatedKernelOpeningState kernel hkernel hactive hq).family) = 0 := by
  let d : Fin 4 →₀ ℕ := Finsupp.single i 1
  have hsource : MvPolynomial.coeff d s.family = 0 := by
    simpa [d] using family_linearCoeff_zero_of_gradientAtZero s.family hgrad i
  have hnot : d ∉ s.family.support :=
    MvPolynomial.notMem_support_iff.mpr hsource
  change
    MvPolynomial.coeff d
      (polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel
          (saturatedKernelSlope kernel s.family hactive)
          (parameterRamificationFamily (K := K)
            (kernelSlopeDenominatorClearingRamification kernel s.family)
            s.family)
          (saturatedKernelSlope_divisibility_afterRamification
            (K := K) kernel s.family hactive))) = 0
  rw [coeff_specialFiber_saturatedKernelBlowup]
  simp [hnot]

/-- Complete Hessian geometry created by a zero-linear-jet saturated kernel
opening.  Unlike the earlier nonlinear-only packet, this also retains the
mixed-Hessian geometry of a kernel-linear first-contact monomial. -/
structure AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  kernel : Fin 4
  kernel_ne : kernel ≠ (0 : Fin 4)
  active : IsActiveKernelCoordinate kernel source.family
  source_free :
    ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
      d kernel = 0
  source_gradient_zero :
    ∀ i : Fin 4,
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i source.family) = 0
  slope_pos : 0 < saturatedKernelSlope kernel source.family active
  opening : ScaleAwareAdaptiveGeometricRestartState (K := K)
  opening_eq :
    opening = source.saturatedKernelOpeningState
      kernel kernel_ne active slope_pos
  exponent : Fin 4 →₀ ℕ
  exponent_mem :
    exponent ∈ (polynomialFamilySpecialFiber opening.family).support
  exponent_kernel_pos : 0 < exponent kernel
  hessianGeometry :
    AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
      (polynomialFamilySpecialFiber opening.family) kernel

/-- Geometry-backed global rank-two progress for the complete first-contact
geometry (diagonal or mixed). -/
structure AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  geometry : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = geometry.opening.withRepairOnly (rankTwoRepairState complexity)
  presentedProgress :
    CertifiedSameScaleEpisodeProgress RR target geometry.opening
  globalProgress :
    AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source

/-- Attach the finite rank promotion only after the actual opening family has
supplied a nonzero Hessian entry involving the newly opened coordinate. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (G : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source) :
    AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress
      RR source complexity := by
  let target := G.opening.withRepairOnly (rankTwoRepairState complexity)
  have hopenRepair : G.opening.repair = rankOneRepairState complexity := by
    rw [G.opening_eq]
    simpa using
      (source.saturatedKernelOpeningState_repair
        G.kernel G.kernel_ne G.active G.slope_pos).trans hsrepair
  have hrepair :
      RepairProgress G.opening.repair (rankTwoRepairState complexity) := by
    simpa [hopenRepair] using rankOne_to_rankTwo_repairProgress complexity
  have hpresented : CertifiedSameScaleEpisodeProgress RR target G.opening := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target source := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    rw [show target.repair = rankTwoRepairState complexity by rfl, hsrepair]
    exact repairState_measure_lt_of_progress
      (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    geometry := G
    target := target
    target_eq := rfl
    presentedProgress := hpresented
    globalProgress := hglobal
  }

/-- **Zero-gradient kernel-free first contact is directly rank-two progress.**

There is no same-scale/unramified alternative in this strengthened interface.
The active saturated face supplies a positive kernel exponent.  Full
source-linear vanishing rules out a lone linear monomial, so A18.4.64 produces
an actual diagonal or mixed Hessian entry on the post-opening family. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeOpening_rankTwoProgress_of_gradientAtZero
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel source.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
        d kernel = 0)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i source.family) = 0) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress
        RR source complexity) := by
  let hq : 0 < saturatedKernelSlope kernel source.family hactive :=
    saturatedKernelSlope_pos kernel source.family hactive hfree
  let opening :=
    source.saturatedKernelOpeningState kernel hkernel hactive hq
  rcases specialFiber_saturatedKernelBlowup_active
      (K := K) kernel source.family hactive with ⟨d, hd, hdpos⟩
  have hdOpening :
      d ∈ (polynomialFamilySpecialFiber opening.family).support := by
    simpa [opening, hq,
      ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpeningState] using hd
  have hlinearOpening :
      ∀ i : Fin 4,
        MvPolynomial.coeff (Finsupp.single i 1)
          (polynomialFamilySpecialFiber opening.family) = 0 := by
    intro i
    simpa [opening] using
      source.saturatedKernelOpeningState_specialFiber_linearCoeff_zero
        kernel hkernel hactive hq hgrad i
  let H := firstContactHessianGeometry_of_linearCoeff_zero
    (polynomialFamilySpecialFiber opening.family)
    hlinearOpening kernel d hdOpening hdpos
  let G : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source := {
    kernel := kernel
    kernel_ne := hkernel
    active := hactive
    source_free := hfree
    source_gradient_zero := hgrad
    slope_pos := hq
    opening := opening
    opening_eq := rfl
    exponent := d
    exponent_mem := hdOpening
    exponent_kernel_pos := hdpos
    hessianGeometry := H
  }
  exact ⟨
    AdaptiveAlignedSmithCanonicalGlobalCompleteKernelOpeningRankTwoProgress.ofGeometry
      RR complexity hsrepair G
  ⟩

end

end HC4.Valuation
