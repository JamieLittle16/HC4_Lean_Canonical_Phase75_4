import HC4.Valuation.AdaptiveAlignedSmithStateBridge
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHomogeneousRigidity
import HC4.Valuation.AdaptiveAlignedSmithSurvivingPacket
import HC4.Valuation.AdaptiveAlignedSmithBoundaryReentry
import Mathlib.Tactic

/-!
# Canonical aligned-Smith local dispatcher

This is the information-preserving replacement for the older five-way local
dispatcher.

Two apparent branches in the old interface were artefacts of forgotten
certificates:

* a canonical blocker already stores one of the four explicit blocker
  patterns, so its normalized axis data reconstructs a concrete residual;
  the zero-base first-wall competition and homogeneous rigidity then force
  an explicit mixed-degree endpoint;
* a surviving integral wall was produced together with a proof that no
  `w`-linear blocker lies on the minimal face.  Once that proof is retained
  by `IntegralAdaptiveSurvivingSmithWall`, symmetric refinement produces the
  persistent quadratic packet directly, with no `refinedBlocker` return.

Thus the honest local output is only

    mixed-degree blocker | persistent packet | canonical re-entry.

No well-founded progress claim is made in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Information-preserving canonical local output. -/
inductive AdaptiveAlignedSmithCanonicalLocalOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  /-- The canonical blocker is forced to be genuinely mixed-degree after
  right longitudinal recentering. -/
  | mixedDegreeBlocker
      (B : AdaptiveAlignedSmithBlockerEndpoint
        (K := K) s.degreeCap)
      (M : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
        (K := K) s.degreeCap)
      (hsame : M.blocker = B)

  /-- A surviving wall goes directly to its persistent minimal quadratic
  packet. -/
  | persistentPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint
        (K := K) s W)

  /-- A section boundary is already coordinate-removable and therefore
  returns an actual ordinary adaptive state. -/
  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

/-- **Canonical three-way local dispatcher.**

This theorem removes the stale `blockerSurvivingShape`, `blockerFirstWall`
and `refinedBlocker` constructors from the reachable canonical path. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalLocalDispatcher
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    AdaptiveAlignedSmithCanonicalLocalOutcome s := by
  rcases s.alignedSmithLegacyClassifierDispatcher with
    hblock | hsurvive | hboundary

  · rcases hblock with ⟨B⟩
    rcases B.exists_mixedDegreeEndpoint_eq with ⟨M, hM⟩
    exact
      AdaptiveAlignedSmithCanonicalLocalOutcome.mixedDegreeBlocker
        B M hM

  · rcases hsurvive with ⟨W⟩
    rcases W.persistentPacket s with ⟨P⟩
    exact
      AdaptiveAlignedSmithCanonicalLocalOutcome.persistentPacket W P

  · rcases hboundary with ⟨B⟩
    exact
      AdaptiveAlignedSmithCanonicalLocalOutcome.reentry
        (s.alignedBoundaryReentry B)

end

end HC4.Valuation
