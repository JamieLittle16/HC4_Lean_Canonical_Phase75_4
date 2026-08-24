import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamifiedProgressUpgrade
import HC4.Valuation.AdaptiveAlignedSmithStateBridge
import HC4.Valuation.AdaptiveAlignedSmithMixedDegreePointedReflection
import Mathlib.Tactic

/-!
# Scale-sound canonical blocker kernel dispatcher

The late rational-kernel normalisation had already proved the correct local
geometry, but the compact blocker endpoint had forgotten the only outer-scale
fact needed to interpret a ramified kernel spend against the incoming state.
The classifier now retains that fact at the point where the aligned endpoint
is created:

    blocker.defect ≤ alignedSmithRamificationIndex * incoming.rawDefect.

This file consumes positive saturated rational slopes *immediately* on the
first canonical blocker, before any later dispatcher can erase that
provenance.  Hence every such slope is returned as an absolute-scale
`CertifiedRamifiedRawDefectSpend` from the actual incoming state.

The sole blocker residue is therefore already in the stationary rational
normal form: mixed degree and saturated slope zero in all three transverse
coordinates.  Surviving-wall and section-boundary branches are merely retained
for their existing downstream consumers; no claim of recursive progress is
made for them here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- A canonical blocker which still remembers its outer aligned clock bound
and has already exhausted every positive saturated rational transverse kernel
slope. -/
structure AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  provenance : AdaptiveAlignedSmithBlockerClockProvenance (K := K) s
  mixed : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint (K := K) s.degreeCap
  mixed_eq : mixed.blocker = provenance.blocker
  allTransverseZero :
    AdaptiveRecenteredAllTransverseZeroRationalSlope provenance.blocker

namespace AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-- The exact blocker retained by the scale-sound stationary package. -/
abbrev blocker
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap :=
  S.provenance.blocker

/-- The stationary blocker's aligned endpoint is bounded by the literal
20-fold outer aligned clock. -/
theorem defect_le_alignedClock
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    S.blocker.aligned.endpoint.defect ≤
      alignedSmithRamificationIndex * s.rawDefect :=
  S.provenance.defect_le

/-- Every transverse coordinate is represented on the honest recentered
special fibre of the scale-sound stationary blocker. -/
theorem specialFiber_witnesses
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) :
    (∃ d ∈
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (1 : Fin 4)) ∧
    (∃ d ∈
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (2 : Fin 4)) ∧
    (∃ d ∈
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support,
      0 < d (3 : Fin 4)) :=
  S.allTransverseZero.specialFiber_witnesses

end AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker

/-- First canonical dispatcher whose blocker-side rational exits are measured
against the *actual incoming scale-aware state*.

The surviving-wall branch also keeps the same outer clock bound.  This will be
useful when its existing packet/re-entry machinery is upgraded to the same
absolute-scale interface. -/
inductive AdaptiveAlignedSmithCanonicalScaleSoundKernelOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | stationaryBlocker
      (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s)

  | survivingWall
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (defect_le :
        W.original.aligned.endpoint.defect ≤
          alignedSmithRamificationIndex * s.rawDefect)

  | sectionBoundary
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K)
        s.degreeCap
        s.rawDefect
        (zeroJetNormalizedFamily s.family)
        s.movingSection)

/-- **Scale-sound first blocker dispatcher.**

A positive saturated rational slope in any transverse coordinate is consumed
as an honest cross-scale defect spend before the blocker can lose its aligned
clock provenance.  Otherwise the blocker is already mixed-degree and has
saturated rational slope zero in coordinates `1`, `2`, and `3`. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalScaleSoundKernelDispatcher
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    AdaptiveAlignedSmithCanonicalScaleSoundKernelOutcome s := by
  rcases s.alignedSmithClassifierDispatcher_withClockBound with
    ⟨B, hclock⟩ | ⟨W, hclock⟩ | ⟨Bboundary⟩

  · let P : AdaptiveAlignedSmithBlockerClockProvenance (K := K) s := {
      blocker := B
      defect_le := hclock
    }
    rcases P.certifiedRamifiedSpend_or_allTransverseZeroRationalSlope with
      hspend | hzero
    · rcases hspend with ⟨target, hcert⟩
      exact .ramifiedSpend target hcert
    · rcases B.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
      exact .stationaryBlocker {
        provenance := P
        mixed := M
        mixed_eq := hM
        allTransverseZero := hzero
      }

  · let W' : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s := {
      original := W
      wall := W.toAdaptiveWall s
      wall_eq := rfl
    }
    exact .survivingWall W' (by simpa [W'] using hclock)

  · rcases Bboundary with ⟨Bboundary⟩
    exact .sectionBoundary Bboundary

end

end HC4.Valuation
