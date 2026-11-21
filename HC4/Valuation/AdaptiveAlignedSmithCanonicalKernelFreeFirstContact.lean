import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveSlopeKernelFree
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyTransverseKernelRestart
import Mathlib.Tactic

/-!
# A18.4.43: consume kernel-free ramified spends by first-contact geometry

Several late A17/A18 adapters end with the same geometric fact: after an
honest determinant-one presentation, the special fibre is independent of a
genuine transverse coordinate.  Historically those adapters immediately
called `exists_certifiedRamifiedRawDefectSpend_of_specialFiber_free`, thereby
forgetting the first-contact face and exporting only a cross-scale rational
clock decrease.

A18.4.39--41 show that this loss of information is unnecessary.  Kernel
freeness makes the saturated slope positive; positive saturated contact is
either already integral on the unramified family, giving literal same-scale
progress, or the denominator-cleared first-contact fibre contains a monomial
quadratic (or higher) in the opened coordinate and hence a nonzero diagonal
Hessian entry.

This file packages that replacement at the exact generic interface used by the
rigid/constant-kernel closing stack.  It deliberately produces no bare
ramified-spend constructor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **Kernel-free first-contact dichotomy.**

Once a genuine transverse coordinate is absent from the special fibre, the
canonical saturated opening is never consumed merely as rational descent.
Either the opening unramifies to an honest same-scale strict successor, or its
new special fibre carries a supported monomial of kernel exponent at least two
and therefore a nonzero diagonal Hessian entry in that coordinate. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeFirstContact_unramified_or_nonlinearHessian
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      let R := kernelSlopeDenominatorClearingRamification kernel s.family
      let q := saturatedKernelSlope kernel s.family hactive
      let Pram := parameterRamificationFamily (K := K) R s.family
      let hdiv := saturatedKernelSlope_divisibility_afterRamification
        (K := K) kernel s.family hactive
      let Fnext := polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel q Pram hdiv)
      ∃ d ∈ Fnext.support,
        2 ≤ d kernel ∧
        MvPolynomial.pderiv kernel (MvPolynomial.pderiv kernel Fnext) ≠ 0 := by
  have hq : 0 < saturatedKernelSlope kernel s.family hactive :=
    saturatedKernelSlope_pos kernel s.family hactive hfree
  exact s.positiveSaturatedKernelOpening_unramified_or_nonlinearHessian
    RR kernel hkernel hactive hq

/-- State-complete form of the same dichotomy.  Hessian defect automatically
supplies activity in any coordinate, so callers which know only special-fibre
kernel freeness do not have to rebuild the active-support witness themselves. -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeFirstContact_unramified_or_nonlinearHessian_of_free
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    let hactive : IsActiveKernelCoordinate kernel s.family :=
      exists_kernelDependentSupport_of_hessianDefect
        (K := K) kernel s.family s.rawDefect s.hessianDefect
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      let R := kernelSlopeDenominatorClearingRamification kernel s.family
      let q := saturatedKernelSlope kernel s.family hactive
      let Pram := parameterRamificationFamily (K := K) R s.family
      let hdiv := saturatedKernelSlope_divisibility_afterRamification
        (K := K) kernel s.family hactive
      let Fnext := polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel q Pram hdiv)
      ∃ d ∈ Fnext.support,
        2 ≤ d kernel ∧
        MvPolynomial.pderiv kernel (MvPolynomial.pderiv kernel Fnext) ≠ 0 := by
  let hactive : IsActiveKernelCoordinate kernel s.family :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) kernel s.family s.rawDefect s.hessianDefect
  exact s.kernelFreeFirstContact_unramified_or_nonlinearHessian
    RR kernel hkernel hactive hfree

end

end HC4.Valuation
