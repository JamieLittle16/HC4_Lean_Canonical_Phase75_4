import HC4.Valuation.AdaptiveAlignedSmithAxisPacketRigidity
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import Mathlib.Tactic

/-!
# A18.4.101: close the blocker all-minors branch without packet escalation

A18.4.100 proves that the three quadratic competitors actually produced by
the all-minors blocker argument are rigid axis-square packets.  The older
helper interface erased the planar axis tag before running the abstract packet
classifier, thereby leaving a spurious rank-two alternative.

This file reruns only that small finite-support producer with the axis tag
retained.  The all-minors branch now has exactly three outputs:

* complete transverse freeness;
* a rigid planar axis-square packet; or
* a rigid `w^2` packet.

The higher-transverse-support case in the pure-longitudinal branch is removed
by the already-green filtration contradiction.  No new recursion or repair
promotion is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Planar packet together with the axis-square provenance that the historical
packet endpoint did not retain. -/
structure AdaptiveAlignedSmithPlanarAxisRigidPacketEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Type (u + 1) where
  packet : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B
  axis : IsPlanarAxisSquareCompetitor packet.competitor
  rigid : HasRigidRankOnePacket
    (0 : Fin 4) 1 2 packet.degree packet.packet

/-- Construct a planar packet while retaining the fact that its singleton
projected exponent is one of the two actual axis squares. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.planarAxisRigidPacket_of_competitor
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (e : SmithSupportExponent)
    (he :
      e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber))
    (haxis : IsPlanarAxisSquareCompetitor e) :
    Nonempty (AdaptiveAlignedSmithPlanarAxisRigidPacketEndpoint (K := K) B) := by
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber
  let T : Finset SmithSupportExponent := {e}

  have hquad :
      (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
      (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
    rcases haxis with hy | hz
    · rw [hy]
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    · rw [hz]
      exact Or.inl ⟨rfl, rfl, rfl⟩

  have hTne : T.Nonempty := ⟨e, by simp [T]⟩
  have hTsub : T ⊆ smithProjectedSupport (1 : Fin 4) 2 3 G := by
    intro q hq
    have hqe : q = e := by simpa [T] using hq
    subst q
    simpa [G] using he
  have hTquad :
      ∀ q ∈ T,
        (q.b = 0 ∧ q.c = 2 ∧ q.d = 0) ∨
        (q.b = 1 ∧ q.c = 1 ∧ q.d = 0) ∨
        (q.b = 2 ∧ q.c = 0 ∧ q.d = 0) := by
    intro q hq
    have hqe : q = e := by simpa [T] using hq
    subst q
    exact hquad

  rcases nonemptyQuadraticProjectedSubface_exists_minimalLongitudinalPacket
      T G hTne hTsub hTquad with
    ⟨D, Q, hprov, hD, hcoll, hhess, hpersist⟩

  let P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B := {
    competitor := e
    competitor_mem := he
    competitor_quadratic := hquad
    degree := D
    packet := Q
    provenance := by simpa [T, G] using hprov
    degree_ge_two := hD
    exactCollision := hcoll
    hessian_zero := hhess
    persistent := hpersist
  }

  have haxisP : IsPlanarAxisSquareCompetitor P.competitor := by
    simpa [P] using haxis
  exact ⟨{
    packet := P
    axis := haxisP
    rigid := P.rigid_of_axisSquare haxisP
  }⟩

/-- Every actual quadratic-axis competitor is already a rigid packet on one
of the planar axes or the `w` axis. -/
inductive AdaptiveAlignedSmithActualQuadraticRigidOutcome
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Type (u + 1)
  | planar (P : AdaptiveAlignedSmithPlanarAxisRigidPacketEndpoint (K := K) B)
  | wSquare
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- Preserve the three-way axis competitor provenance before constructing the
packet. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.actualQuadraticRigidOutcome
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hcomp : HasRightRecenteredQuadraticAxisCompetitor B) :
    Nonempty (AdaptiveAlignedSmithActualQuadraticRigidOutcome (K := K) B) := by
  rcases hcomp with h20 | h02 | hw
  · rcases B.planarAxisRigidPacket_of_competitor
      ({ b := 2, c := 0, d := 0 } : SmithSupportExponent)
      h20 (Or.inl rfl) with ⟨P⟩
    exact ⟨.planar P⟩
  · rcases B.planarAxisRigidPacket_of_competitor
      ({ b := 0, c := 2, d := 0 } : SmithSupportExponent)
      h02 (Or.inr rfl) with ⟨P⟩
    exact ⟨.planar P⟩
  · rcases B.wSquarePacket hw with ⟨P⟩
    exact ⟨.wSquare P P.rigid⟩

/-- Exact all-minors outcome after removing the spurious packet escalation. -/
inductive AdaptiveAlignedSmithAllMinorsRigidOutcome
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Prop
  | transverseFree
      (free :
        ∀ d ∈ B.aligned.endpoint.rawSpecialFiber.support,
          d (1 : Fin 4) = 0 ∧ d (2 : Fin 4) = 0 ∧ d (3 : Fin 4) = 0)
  | planarRigid
      (P : AdaptiveAlignedSmithPlanarAxisRigidPacketEndpoint (K := K) B)
  | wSquareRigid
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (rigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

namespace AdaptiveAlignedSmithBlockerEndpoint

/-- Turn a retained quadratic-axis competitor into the corresponding
all-minors rigid output. -/
theorem allMinorsRigidOutcome_of_quadraticCompetitor
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hcomp : HasRightRecenteredQuadraticAxisCompetitor B) :
    AdaptiveAlignedSmithAllMinorsRigidOutcome (K := K) B := by
  rcases B.actualQuadraticRigidOutcome hcomp with ⟨R⟩
  cases R with
  | planar P => exact .planarRigid P
  | wSquare P hrigid => exact .wSquareRigid P hrigid

/-- **Complete rigid closure of the all-minors blocker branch.** -/
theorem allMinorsRigidOutcome
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    AdaptiveAlignedSmithAllMinorsRigidOutcome (K := K) B := by
  rcases B.pureLongitudinal_or_quadraticCompetitor_of_allMinors hall with
    hpure | hcomp
  · rcases B.pureLongitudinal_curvature_and_support_frontier hpure with
      ⟨_P, _hcurv, hfree | hpos⟩
    · exact .transverseFree hfree
    · by_cases hlin : HasRightRecenteredTransverseLinearCompetitor B
      · exact B.allMinorsRigidOutcome_of_quadraticCompetitor
          (B.quadraticCompetitor_of_transverseLinear_of_allMinors hall hlin)
      · have hposG :
            ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3
                (longitudinalRightRecenterHom
                  (K := K) B.aligned.endpoint.rawSpecialFiber),
              HasPositiveTotalTransverseDegree e := by
          rcases hpos with ⟨e, he, hdeg⟩
          refine ⟨e, ?_, hdeg⟩
          have hsupport :=
            smithProjectedSupport_longitudinalRightRecenterHom
              B.aligned.endpoint.rawSpecialFiber
          rw [hsupport]
          exact he
        have hhigher : HasRightRecenteredHigherTransverseSupport B :=
          ⟨hlin, hposG⟩
        exact False.elim
          (B.no_higherTransverseSupport_of_pureLongitudinal_allMinors
            hpure hall hhigher)
  · exact B.allMinorsRigidOutcome_of_quadraticCompetitor hcomp

end AdaptiveAlignedSmithBlockerEndpoint

end

end HC4.Valuation
