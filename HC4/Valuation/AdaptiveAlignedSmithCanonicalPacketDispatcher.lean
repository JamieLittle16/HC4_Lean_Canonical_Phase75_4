import HC4.Valuation.AdaptiveAlignedSmithCanonicalLocalDispatcher
import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoSaturated
import HC4.Valuation.AdaptiveSectionBoundaryReentry
import HC4.Valuation.AdaptiveAlignedSmithRankTwoZeroSchurComplete
import Mathlib.Tactic

/-!
# Canonical packet-expanded aligned-Smith dispatcher

This is the packet-expanded version of the information-preserving canonical
three-way dispatcher.

Compared with `AdaptiveAlignedSmithPacketExpandedOutcome`, the following
stale branches have disappeared from the reachable canonical path:

* `blockerSurvivingShape`;
* arbitrary-base `blockerFirstWall`;
* `refinedBlocker`.

The sole blocker output is the explicit mixed-degree endpoint belonging to
the actual blocker.  The surviving-wall output is consumed immediately by
the persistent-packet machinery.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

inductive AdaptiveAlignedSmithCanonicalPacketOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | mixedDegreeBlocker
      (B : AdaptiveAlignedSmithBlockerEndpoint
        (K := K) s.degreeCap)
      (M : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
        (K := K) s.degreeCap)
      (hsame : M.blocker = B)

  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

  | degreeTwoSaturated
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint
        (K := K) s W)
      (hD : P.degree = 2)
      (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint
        (K := K) s W)

  | rigidPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint
        (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint
        (K := K) s W P)

  | rankTwoZeroSchur
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint
        (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
        (K := K) s W P complexity)
      (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
        (K := K) s W P complexity R2)

/-- **Reduced packet-expanded canonical dispatcher.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalPacketDispatcher
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalPacketOutcome s complexity := by
  rcases s.alignedSmithCanonicalLocalDispatcher with
    ⟨B, M, hsame⟩ | ⟨W, P⟩ | ⟨t⟩

  · exact
      AdaptiveAlignedSmithCanonicalPacketOutcome.mixedDegreeBlocker
        B M hsame

  · rcases P.degree_eq_two_or_three_le s W with hD2 | hD3

    · rcases
        P.degreeTwo_zeroDefect_or_boundary_or_saturated
          s W hD2 with
        hzero | hboundary | hsaturated

      · exact
          AdaptiveAlignedSmithCanonicalPacketOutcome.zeroDefect
            (W.original.aligned.toAdaptiveState s) hzero

      · rcases hboundary with ⟨Bboundary⟩
        exact
          AdaptiveAlignedSmithCanonicalPacketOutcome.reentry
            Bboundary.exposure.boundaryShearedAdaptiveState

      · rcases hsaturated with ⟨S⟩
        exact
          AdaptiveAlignedSmithCanonicalPacketOutcome.degreeTwoSaturated
            W P hD2 S

    · rcases
        P.rigid_or_rankTwoFamilyContinuation
          s W complexity with
        hrigid | hrankTwo

      · rcases hrigid with ⟨R⟩
        exact
          AdaptiveAlignedSmithCanonicalPacketOutcome.rigidPacket
            W P hD3 R

      · rcases hrankTwo with ⟨R2⟩
        rcases
            R2.zeroDefect_or_matrixExposure
              s W P complexity with
          hzero | hmatrix

        · exact
            AdaptiveAlignedSmithCanonicalPacketOutcome.zeroDefect
              (P.rankOneAnalysisState s W complexity) hzero

        · rcases hmatrix with ⟨M⟩
          exact
            AdaptiveAlignedSmithCanonicalPacketOutcome.rankTwoZeroSchur
              W P hD3 R2 M

  · exact AdaptiveAlignedSmithCanonicalPacketOutcome.reentry t

end

end HC4.Valuation
