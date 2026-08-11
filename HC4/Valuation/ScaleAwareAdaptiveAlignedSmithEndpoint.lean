import HC4.Valuation.AdaptiveAlignedSmithEndpoint
import HC4.Valuation.CanonicalAdaptiveSmithWall

/-!
# Scale-aware adaptive aligned-Smith endpoint

The mixed-degree aligned-Smith macro is state-neutral.  This file attaches it
to the scale-aware adaptive geometric state through zero-jet normalization.

No new progress claim is made here.  In particular, this wrapper does not
use `rawDefect / scale`.  It only supplies the exact geometry needed by the
future dispatcher.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- Zero-jet normalization preserves the exact raw Hessian clock of a
scale-aware adaptive state. -/
theorem ScaleAwareAdaptiveGeometricRestartState.normalized_hessianDefect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    HasPolynomialFamilyHessianDefect
      (K := K) (zeroJetNormalizedFamily s.family) s.rawDefect :=
  polynomialFamilyHessianDefect_zeroJetNormalizedFamily
    s.family s.rawDefect s.hessianDefect

/-- Zero-jet normalization preserves the global nonlinear source-degree cap
of a scale-aware adaptive state. -/
theorem ScaleAwareAdaptiveGeometricRestartState.normalized_nonlinearDegreeBound
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    HC4.Newton.NonlinearDegreeBound s.degreeCap
      (zeroJetNormalizedFamily s.family) :=
  nonlinearDegreeBound_zeroJetNormalizedFamily
    s.family s.degreeCap s.nonlinearDegreeBound

/-- Zero-jet normalization preserves the state's exact zero-left collision. -/
theorem ScaleAwareAdaptiveGeometricRestartState.normalized_exactCollision
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    HasPolynomialFamilyExactGradientCollision
      (zeroJetNormalizedFamily s.family)
      (zeroPolynomialSection (K := K))
      s.movingSection := by
  simpa [zeroPolynomialSection] using
    polynomialFamilyExactGradientCollision_zeroJetNormalizedFamily
      s.family
      (fun _ : Fin 4 => (0 : Polynomial K))
      s.movingSection
      s.exactCollision

/-- **Scale-aware mixed-degree aligned-Smith macro.**

Apply the finite aligned-Smith endpoint theorem to the zero-jet-normalized
actual family retained by a scale-aware adaptive state.

The result is either

* a symmetric-minimal geometry-carrying endpoint with canonical zero-left
  collision and right special point `e0`; or
* an actual aligned right-section boundary carrying the transformed family,
  exact clock, degree cap, and collision.

This theorem deliberately makes no global progress assertion and does not
alter or compare `s.scale`.  The later dispatcher can attach the correct
post-ramification scale to whichever endpoint it consumes. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithEndpoint
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    Nonempty
        (AdaptiveAlignedSmithMinimalEndpoint
          (K := K) s.degreeCap) ∨
      Nonempty
        (AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K)
          s.degreeCap
          s.rawDefect
          (zeroJetNormalizedFamily s.family)
          s.movingSection) := by
  exact
    adaptiveAlignedSmithEndpoint_zeroLeft
      (K := K)
      s.degreeCap
      (zeroJetNormalizedFamily s.family)
      s.movingSection
      s.rawDefect
      s.normalized_hessianDefect
      s.normalized_nonlinearDegreeBound
      s.normalized_exactCollision
      s.sectionSpecial

end

end HC4.Valuation
