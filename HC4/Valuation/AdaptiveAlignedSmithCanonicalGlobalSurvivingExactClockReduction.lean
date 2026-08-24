import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingRankTwoAbsoluteScale
import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoSaturated
import HC4.Valuation.AdaptiveAlignedSmithSurvivingPacket
import Mathlib.Tactic

/-!
# A18.4.8: reduce one surviving-exact-clock presentation leaf

A18.4.7 made the rank-two continuation of a surviving aligned packet honest at
its actual absolute scale.  We can now return to the provenance trace and
consume the `survivingExactClock` leaf itself far enough that no zero-clock or
rank-two ambiguity remains.

For the retained surviving wall we first extract its canonical persistent
packet.  Its degree is either `2` or at least `3`.

* In degree `2`, the already-green local theorem gives zero defect, a genuine
  section boundary, or the saturated first-contact endpoint.  Zero defect is
  reflected through the certified aligned presentation all the way back to
  the original source.
* In degree at least `3`, the packet is rigid or has an actual rank-two family
  continuation.  The latter is exactly the A18.4.7 absolute-scale macro.

Thus a surviving-exact-clock provenance leaf is reduced to only three pieces
of still-unconsumed geometry: degree-two boundary, degree-two saturation, or
an actual rigid packet.  No presentation is declared progress and no scale is
reset to `1`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Remaining geometry after directly consuming the zero-clock and rank-two
subbranches of one `survivingExactClock` provenance leaf. -/
inductive AdaptiveAlignedSmithCanonicalGlobalSurvivingExactClockOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | degreeTwoBoundary
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : P.degree = 2)
      (B : AdaptiveAlignedSmithDegreeTwoBoundaryEndpoint (K := K) s W)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | degreeTwoSaturated
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : P.degree = 2)
      (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint (K := K) s W)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

  | rigidPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
      (clock_eq :
        W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)

/-- Zero determinant clock on the aligned ordinary state reflects to zero
raw defect on the original scale-aware source, because the aligned outer move
is a certified pure ramified presentation. -/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.source_rawDefect_eq_zero_of_aligned
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (clock_eq :
      W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hzero : (W.original.aligned.toAdaptiveState s).defect = 0) :
    s.rawDefect = 0 := by
  let outer := W.original.aligned.toOuterScaleAwareState s
  have hmove : HasCertifiedRamifiedEpisodeInternalMove outer s := by
    exact
      ⟨W.original.aligned.certifiedOuterInternal_of_defect_eq
        s clock_eq⟩
  have houterZero : outer.rawDefect = 0 := by
    simpa [outer] using hzero
  exact hmove.source_rawDefect_eq_zero_of_target houterZero

/-- **One surviving-exact-clock trace leaf is now substantially consumed.**

The persistent packet is canonical.  Zero-clock alternatives are reflected
back to the original source, and every actual rank-two family continuation is
turned into the source-honest absolute-scale macro of A18.4.7.  Only the
three genuinely unresolved geometric packet types remain. -/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.globalExactClockReduction
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (complexity : ℕ)
    (clock_eq :
      W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingExactClockOutcome
      RR s complexity := by
  rcases W.persistentPacket s with ⟨P⟩
  rcases P.degree_eq_two_or_three_le s W with hD2 | hD3

  · rcases
      P.degreeTwo_zeroDefect_or_boundary_or_saturated
        s W hD2 with
      hzero | hboundary | hsaturated

    · have hsZero : s.rawDefect = 0 :=
        W.source_rawDefect_eq_zero_of_aligned clock_eq hzero
      exact
        .zeroDefectReentry hsZero
          (s.exists_globalZeroDefectReentryData hsZero)

    · rcases hboundary with ⟨B⟩
      exact .degreeTwoBoundary W P hD2 B clock_eq

    · rcases hsaturated with ⟨S⟩
      exact .degreeTwoSaturated W P hD2 S clock_eq

  · rcases
      P.rigid_or_rankTwoFamilyContinuation
        s W complexity with
      hrigid | hrankTwo

    · rcases hrigid with ⟨R⟩
      exact .rigidPacket W P hD3 R clock_eq

    · rcases hrankTwo with ⟨R2⟩
      exact
        .ramifiedStrictMacro
          (R2.globalRamifiedStrictMacro_of_survivingExactClock
            RR clock_eq hsrepair)

end

end HC4.Valuation
