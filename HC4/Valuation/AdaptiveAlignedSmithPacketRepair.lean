import HC4.Valuation.AdaptiveAlignedSmithSurvivingPacket
import Mathlib.Tactic

/-!
# Persistent aligned-Smith packet to rigid or rank-two family continuation

The surviving-wall dispatcher now extracts a minimal homogeneous packet `Q`
with persistent rank-one Smith support.  The existing rank-one packet
classifier is indexed by the abstract repair state `rankOneRepairState`.

The aligned dispatcher deliberately did not pretend that the incoming global
state had already reached that repair coordinate.  We therefore introduce a
*same-family analysis view*: only the bookkeeping field `repair` is set to
`rankOneRepairState complexity`; the actual polynomial family, determinant
clock, collision, degree cap, source complexity and normalized special fibre
are unchanged.

This is not asserted to be a geometric successor.  The genuine repair
progress is supplied afterwards by the already-proved theorem
`rankOnePersistentPacket_rigid_or_rankTwoProgress`.

In the rank-two alternative we immediately reuse
`AdaptiveRankTwoContinuation.withFamilyProvenance`, retaining the exact
integral surviving wall and the exact balanced Smith subface from which the
packet was extracted.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Same-family rank-one analysis view -/

/-- Reindex only the finite repair-stage bookkeeping; no polynomial geometry
is changed.  This object is an analysis view, not by itself a claimed
successor. -/
noncomputable def
    AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ) :
    AdaptiveGeometricRestartState (K := K) :=
  (W.original.aligned.toAdaptiveState s).withRepair
    (rankOneRepairState complexity)

@[simp]
theorem
    AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState_repair
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ) :
    (P.rankOneAnalysisState s W complexity).repair =
      rankOneRepairState complexity := rfl

@[simp]
theorem
    AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState_family
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ) :
    (P.rankOneAnalysisState s W complexity).family =
      (W.original.aligned.toAdaptiveState s).family := rfl

@[simp]
theorem
    AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState_defect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ) :
    (P.rankOneAnalysisState s W complexity).defect =
      (W.original.aligned.toAdaptiveState s).defect := rfl

@[simp]
theorem
    AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState_normalizedSpecialFiber
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ) :
    (P.rankOneAnalysisState s W complexity).normalizedSpecialFiber =
      (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber := rfl

/-! ## Dispatcher output objects -/

/-- Rigid packet alternative, retaining the exact packet endpoint that
produced it. -/
structure AdaptiveAlignedSmithRigidPacketEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W) where
  rigid :
    HasRigidRankOnePacket
      (0 : Fin 4) 1 2 P.degree P.packet

/-- Rank-two packet alternative with the *same wall* and *same balanced
subface* packaged into the existing actual-family continuation interface. -/
structure AdaptiveAlignedSmithRankTwoPacketEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ) where
  continuation :
    AdaptiveRankTwoFamilyContinuation
      (P.rankOneAnalysisState s W complexity)
      P.degree complexity P.packet

/-- The packet degree is either the exceptional quadratic value `2`, or is
at least `3`.  This is deliberately kept as an explicit dispatcher split:
degree two belongs to the saturated-kernel route, while the old rigid/rank-two
closing machinery is naturally used from degree three onward. -/
theorem AdaptiveAlignedSmithPersistentPacketEndpoint.degree_eq_two_or_three_le
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W) :
    P.degree = 2 ∨ 3 ≤ P.degree := by
  have hD : 2 ≤ P.degree := P.degree_ge_two
  omega

/-! ## Existing rank-one classifier, with family provenance retained -/

/-- **Persistent packet -> rigid or rank-two family continuation.**

No geometric restart is invented here.  The rank-one analysis state has the
same family as the aligned endpoint, and the strict repair progress in the
rank-two branch is exactly the existing intrinsic packet progress theorem.

The rank-two output already retains:

* the exact integral surviving wall;
* equality of its subface with that wall's balanced Smith face;
* the quadratic face shape;
* minimal longitudinal packet provenance;
* persistent rank-one support.

It is therefore ready for the existing actual-family matrix exposure. -/
theorem
    AdaptiveAlignedSmithPersistentPacketEndpoint.rigid_or_rankTwoFamilyContinuation
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ) :
    Nonempty
        (AdaptiveAlignedSmithRigidPacketEndpoint
          (K := K) s W P) ∨
      Nonempty
        (AdaptiveAlignedSmithRankTwoPacketEndpoint
          (K := K) s W P complexity) := by
  let a0 := W.original.aligned.toAdaptiveState s
  let a1 := P.rankOneAnalysisState s W complexity

  have hQne : P.packet ≠ 0 :=
    P.provenance.packet_ne_zero

  rcases
      rankOnePersistentPacket_rigid_or_rankTwoProgress
        (complexity := complexity)
        finFour_zero_ne_one
        finFour_zero_ne_two
        finFour_one_ne_two
        P.persistent
        hQne with
    hrigid | hrepair

  · exact Or.inl ⟨{ rigid := hrigid }⟩

  · right

    have hcont :
        AdaptiveRankTwoContinuation
          a1 P.degree complexity P.packet := by
      refine
        { packet_ne_zero := hQne
          degree_ge_two := P.degree_ge_two
          homogeneous := P.provenance.packet_homogeneous
          exactCollision := P.exactCollision
          hessian_zero := P.hessian_zero
          escalation := hrepair.1
          repairProgress := ?_ }
      simpa [a1,
        AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState]
        using hrepair.2

    let T := W.balancedSubface s

    have hT :
        T =
          smithSymmetricBalancedSubface
            (smithProjectedSupport
              (1 : Fin 4) 2 3 a1.normalizedSpecialFiber)
            W.wall.level W.wall.base := by
      rfl

    have hquad :
        ∀ e ∈ T,
          (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
          (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
          (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
      intro e he
      exact P.quadratic e (by simpa [T] using he)

    have hprov :
        IsMinimalLongitudinalSmithPacket
          T a1.normalizedSpecialFiber P.degree P.packet := by
      change
        IsMinimalLongitudinalSmithPacket
          (W.balancedSubface s)
          a0.normalizedSpecialFiber
          P.degree P.packet
      exact P.provenance

    have hfamily :
        AdaptiveRankTwoFamilyContinuation
          a1 P.degree complexity P.packet :=
      hcont.withFamilyProvenance
        W.wall T hT hquad hprov

    exact
      ⟨{
        continuation := hfamily
      }⟩

end

end HC4.Valuation
