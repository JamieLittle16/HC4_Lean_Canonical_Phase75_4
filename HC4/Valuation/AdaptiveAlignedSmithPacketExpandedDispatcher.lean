import HC4.Valuation.AdaptiveAlignedSmithLocalDispatcher
import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoSaturated
import HC4.Valuation.AdaptiveSectionBoundaryReentry
import HC4.Valuation.AdaptiveAlignedSmithRankTwoZeroSchurComplete
import Mathlib.Tactic

/-!
# Packet-expanded aligned-Smith dispatcher

This is the second assembly layer of the adaptive aligned-Smith engine.

The first local dispatcher still exposed a `persistentPacket` constructor.
That constructor is now consumed completely using the already-green packet
machinery.

For a persistent packet `P`:

* `P.degree = 2` enters the saturated-kernel branch and yields
  - zero defect,
  - a section boundary which is immediately canonicalised by the
    determinant-one boundary shear, or
  - a scale-aware saturated first-contact state with genuine positive
    `x₃` support;

* `3 ≤ P.degree` enters the rank-one classifier and yields
  - a rigid packet, or
  - a rank-two actual-family continuation.
    The rank-two continuation yields either zero defect or an actual matrix
    exposure, and every such matrix exposure reaches automatic exact
    zero-Schur data with strictly positive first Schur order.

No global well-foundedness assertion is made here.  In particular, the
generic `reentry` and `degreeTwoSaturated` constructors are geometric
successors, but are not yet declared smaller than the incoming scale-aware
state.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Dispatcher after completely consuming the persistent-packet constructor
of `AdaptiveAlignedSmithLocalOutcome`.

The constructors are deliberately geometric rather than measure-theoretic.
This keeps the local theorem honest while making the remaining global
obligations explicit.
-/
inductive AdaptiveAlignedSmithPacketExpandedOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (base : SmithSupportExponent → ℤ)
    (complexity : ℕ) : Prop

  | blockerSurvivingShape
      (B : AdaptiveAlignedSmithBlockerEndpoint
        (K := K) s.degreeCap)
      (shape : HasGeneralSurvivingSmithGradeShape B.exponent)

  | blockerFirstWall
      (B : AdaptiveAlignedSmithBlockerEndpoint
        (K := K) s.degreeCap)
      (wall :
        HasAlignedRecenteredFirstWallCompetition
          B.aligned.endpoint.rawSpecialFiber B.exponent base)

  | refinedBlocker
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (B : AdaptiveAlignedSmithRefinedBlockerEndpoint
        (K := K) s W)

  /-- A genuine ordinary adaptive state obtained by a coordinate-removable
  section-boundary re-entry. -/
  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

  /-- A concrete adaptive state whose exact Hessian clock has reached zero.
  The state itself is retained so the later zero-defect audit can be generic
  rather than branch-specific. -/
  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

  /-- Exceptional degree-two packet after the already-proved saturated
  first-contact construction.  Its `stage` field contains the actual
  scale-aware successor with positive `x₃` support. -/
  | degreeTwoSaturated
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint
        (K := K) s W)
      (hD : P.degree = 2)
      (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint
        (K := K) s W)

  /-- Degree at least three, with a genuine rigid rank-one packet. -/
  | rigidPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint
        (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint
        (K := K) s W P)

  /-- Degree at least three, with an actual rank-two matrix exposure.
  Under `[CharZero K]`, the already-green automatic zero-Schur theorem turns
  `M` into exact zero-Schur data with strictly positive first Schur order.
  We deliberately store only the geometric matrix exposure here so that the
  outcome type itself does not require a `CharZero` instance. -/
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

/-- **Packet-expanded local dispatcher.**

This theorem consumes the `persistentPacket` output of
`alignedSmithLocalDispatcher` all the way through the exceptional
degree-two saturation or the degree-at-least-three rigid/rank-two
zero-Schur split.

Both kinds of section boundary encountered on this route are converted to
ordinary adaptive re-entry states before being returned.
-/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithPacketExpandedDispatcher
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (base : SmithSupportExponent → ℤ)
    (complexity : ℕ) :
    AdaptiveAlignedSmithPacketExpandedOutcome s base complexity := by
  rcases s.alignedSmithLocalDispatcher base with
    ⟨B, hshape⟩ |
    ⟨B, hfirst⟩ |
    ⟨W, Brefined⟩ |
    ⟨W, P⟩ |
    ⟨Bboundary⟩

  · exact
      AdaptiveAlignedSmithPacketExpandedOutcome.blockerSurvivingShape
        B hshape

  · exact
      AdaptiveAlignedSmithPacketExpandedOutcome.blockerFirstWall
        B hfirst

  · exact
      AdaptiveAlignedSmithPacketExpandedOutcome.refinedBlocker
        W Brefined

  ·
    rcases P.degree_eq_two_or_three_le s W with hD2 | hD3

    · rcases
        P.degreeTwo_zeroDefect_or_boundary_or_saturated
          s W hD2 with
        hzero | hboundary | hsaturated

      · exact
          AdaptiveAlignedSmithPacketExpandedOutcome.zeroDefect
            (W.original.aligned.toAdaptiveState s) hzero

      · rcases hboundary with ⟨B⟩
        exact
          AdaptiveAlignedSmithPacketExpandedOutcome.reentry
            B.exposure.boundaryShearedAdaptiveState

      · rcases hsaturated with ⟨S⟩
        exact
          AdaptiveAlignedSmithPacketExpandedOutcome.degreeTwoSaturated
            W P hD2 S

    · rcases
        P.rigid_or_rankTwoFamilyContinuation
          s W complexity with
        hrigid | hrankTwo

      · rcases hrigid with ⟨R⟩
        exact
          AdaptiveAlignedSmithPacketExpandedOutcome.rigidPacket
            W P hD3 R

      · rcases hrankTwo with ⟨R2⟩
        rcases
            R2.zeroDefect_or_matrixExposure
              s W P complexity with
          hzero | hmatrix

        · exact
            AdaptiveAlignedSmithPacketExpandedOutcome.zeroDefect
              (P.rankOneAnalysisState s W complexity) hzero

        · rcases hmatrix with ⟨M⟩
          exact
            AdaptiveAlignedSmithPacketExpandedOutcome.rankTwoZeroSchur
              W P hD3 R2 M

  · exact
      AdaptiveAlignedSmithPacketExpandedOutcome.reentry
        (s.alignedBoundaryReentry Bboundary)


/-- The `rankTwoZeroSchur` geometric output automatically carries exact
zero-Schur data with positive first Schur order once characteristic zero is
available.  Keeping this as a theorem rather than an inductive field avoids
forcing `CharZero K` into the dispatcher outcome type itself. -/
theorem AdaptiveAlignedSmithRankTwoMatrixEndpoint.packetExpanded_zeroSchur_firstOrder_pos
    [CharZero K]
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {base : SmithSupportExponent → ℤ}
    {complexity : ℕ}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    (hD : 3 ≤ P.degree)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2) :
    0 <
      (M.toExactZeroSchurAutomatic
        s W P complexity R2 hD).toClock.firstOrder := by
  exact M.zeroSchur_firstOrder_pos s W P complexity R2 hD

end

end HC4.Valuation
