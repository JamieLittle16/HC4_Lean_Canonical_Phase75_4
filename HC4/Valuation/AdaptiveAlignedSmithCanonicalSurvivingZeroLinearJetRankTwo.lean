import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedZeroLinearJetKernelOpening
import Mathlib.Tactic

/-!
# A18.4.68: kernel-free surviving exposure is directly rank two

A18.4.52 retained a same-scale escape from the exposed surviving-wall state.
That escape came solely from the kernel-linear first-contact alternative.
A18.4.65--66 remove it once the exposed family is known to have zero source
linear jet.

The adaptive Smith exposure is constructed from a zero-jet-normalized family
and introduces no new source exponent, so A18.4.66 already proves that its
actual family retains `HasZeroSourceJet`.  Therefore every kernel-free
canonical surviving exposure goes directly to diagonal-or-mixed first-contact
Hessian geometry and hence to a geometry-backed rank-two target.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **Canonical kernel-free surviving exposure gives direct rank-two
progress.**

All presentation scales are retained as provenance only.  The actual exposed
family has zero source jet and coordinate `3` absent from its special fibre;
A18.4.66 therefore promotes the saturated-opening family by genuine Hessian
geometry, with no presented same-scale recursive alternative. -/
theorem AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint.completeRankTwoProgress_from_presented
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
      (K := K) D.presented)
    (hclock : E.W.original.aligned.endpoint.defect = D.presented.rawDefect)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalGlobalPresentedCompleteKernelOpeningRankTwoProgress
        RR source complexity) := by
  let s := D.presented
  let a : AdaptiveGeometricRestartState (K := K) :=
    E.exposure.toAdaptiveState E.canonicalSpecial
  let exposed := a.toScaleAwareAt
    (E.exposure.ramification.R * s.scale)
    (Nat.mul_pos E.exposure.ramification.R_pos s.scale_pos)

  have hexposed : HasCertifiedRamifiedEpisodeInternalMove exposed s := by
    simpa [exposed, a, s] using
      E.exposure.certifiedInternalMove_from_presented
        E.W E.canonicalSpecial hclock

  have hsource : HasCertifiedRamifiedEpisodeInternalMove exposed source :=
    D.sourcePresentation.trans hexposed

  have hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber exposed.family).support,
        d (3 : Fin 4) = 0 := by
    simpa [exposed, a] using E.specialFiber_free_three

  have hactive : IsActiveKernelCoordinate (3 : Fin 4) exposed.family :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) (3 : Fin 4) exposed.family exposed.rawDefect exposed.hessianDefect

  have hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i exposed.family) = 0 := by
    intro i
    simpa [exposed, a] using E.exposure.zeroSourceJet.gradientAtZero i

  exact source.presentedKernelFree_rankTwoProgress_of_gradientAtZero
    RR exposed complexity hsrepair hsource
    (3 : Fin 4) (by decide) hactive hfree hgrad

end

end HC4.Valuation
