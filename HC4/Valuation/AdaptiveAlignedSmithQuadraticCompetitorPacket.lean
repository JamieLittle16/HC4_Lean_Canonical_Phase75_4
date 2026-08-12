import HC4.Valuation.AdaptiveAlignedSmithRankOneQuadraticCompetitor
import HC4.Newton.MixedDegreeWallRefinement
import HC4.Newton.RankOneRepairProgress
import Mathlib.Tactic

/-!
# Planar quadratic competitor to persistent packet

The exceptional finite-Hessian branch now produces one of three explicit
quadratic projected-support competitors after right recentering:

* `(2,0,0)`;
* `(0,2,0)`;
* `(0,0,2)`.

The first two are already members of the symmetric quadratic Smith target.
No new wall construction is needed: the singleton subface containing the
actual competitor is a nonempty quadratic projected subface, so the existing
minimal-longitudinal-packet theorem applies directly.

Thus the two planar competitors immediately produce a genuine homogeneous
persistent packet carrying exact collision and zero Hessian determinant, and
hence enter the existing rigid/rank-two packet classifier.

Only the positive-grade `w^2` competitor and the genuinely pure-longitudinal
blocker remain outside this packet handoff.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A persistent packet extracted directly from a singleton planar quadratic
competitor in the right-recentered blocker special fibre. -/
structure AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) where
  competitor : SmithSupportExponent
  competitor_mem :
    competitor ∈
      smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber)
  competitor_quadratic :
    (competitor.b = 0 ∧ competitor.c = 2 ∧ competitor.d = 0) ∨
    (competitor.b = 1 ∧ competitor.c = 1 ∧ competitor.d = 0) ∨
    (competitor.b = 2 ∧ competitor.c = 0 ∧ competitor.d = 0)
  degree : ℕ
  packet : MvPolynomial (Fin 4) K
  provenance :
    IsMinimalLongitudinalSmithPacket
      {competitor}
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber)
      degree packet
  degree_ge_two : 2 ≤ degree
  exactCollision :
    HasExactGradientCollision packet
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
  hessian_zero : HC4.Polynomial.hessianDeterminant packet = 0
  persistent :
    HasRankOnePersistentPacketSupport
      (0 : Fin 4) 1 2 degree packet

/-- Any actual planar quadratic competitor gives a singleton persistent
packet, with full provenance in the right-recentered special fibre. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.packet_of_planarQuadraticCompetitor
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (e : SmithSupportExponent)
    (he :
      e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber))
    (hquad :
      (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
      (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)) :
    Nonempty
      (AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) B) := by
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber
  let T : Finset SmithSupportExponent := {e}

  have hTne : T.Nonempty := by
    exact ⟨e, by simp [T]⟩

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

  rcases
      nonemptyQuadraticProjectedSubface_exists_minimalLongitudinalPacket
        T G hTne hTsub hTquad with
    ⟨D, Q, hprov, hD, hcoll, hhess, hpersist⟩

  exact
    ⟨{
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
    }⟩

/-- The competitor trichotomy is sharpened: either one of the two planar
quadratic competitors already yields a persistent packet, or the only
remaining competitor is the positive-grade `w^2` exponent. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.packet_or_wSquare_of_quadraticCompetitor
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hcomp : HasRightRecenteredQuadraticAxisCompetitor B) :
    Nonempty
        (AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
          (K := K) B) ∨
      ({ b := 0, c := 0, d := 2 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber) := by
  rcases hcomp with h20 | h02 | hw2
  · left
    exact B.packet_of_planarQuadraticCompetitor
      ({ b := 2, c := 0, d := 0 } : SmithSupportExponent)
      h20 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  · left
    exact B.packet_of_planarQuadraticCompetitor
      ({ b := 0, c := 2, d := 0 } : SmithSupportExponent)
      h02 (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact Or.inr hw2

/-- Consequently, the all-minors blocker branch is reduced to exactly three
honest outputs: pure longitudinal, an actual persistent packet, or `w^2`. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.pureLongitudinal_or_packet_or_wSquare_of_allMinors
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero) :
    IsPureLongitudinalSmithPattern B.exponent ∨
      Nonempty
        (AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
          (K := K) B) ∨
      ({ b := 0, c := 0, d := 2 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber) := by
  rcases B.pureLongitudinal_or_quadraticCompetitor_of_allMinors hall with
    hpure | hcomp
  · exact Or.inl hpure
  · right
    exact B.packet_or_wSquare_of_quadraticCompetitor hcomp

/-- Local algebraic outcome for a packet extracted from a quadratic
competitor.  The rank-two alternative includes the intrinsic strict repair
progress already proved by the rank-one packet classifier. -/
inductive AdaptiveAlignedSmithQuadraticCompetitorPacketLocalOutcome
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
      (K := K) B)
    (complexity : ℕ) : Prop
  | rigid
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)
  | rankTwo
      (hesc : HasRankTwoPacketEscalation
        (0 : Fin 4) 1 2 P.degree P.packet)
      (hprogress :
        RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity))

/-- **Planar quadratic competitor -> existing packet classifier.** -/
theorem AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint.localOutcome
    [CharZero K]
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
      (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithQuadraticCompetitorPacketLocalOutcome
      P complexity := by
  rcases
      rankOnePersistentPacket_rigid_or_rankTwoProgress
        (complexity := complexity)
        (by decide)
        (by decide)
        (by decide)
        P.persistent
        P.provenance.packet_ne_zero with
    hrigid | hrankTwo
  · exact .rigid hrigid
  · exact .rankTwo hrankTwo.1 hrankTwo.2

/-- Dispatcher-facing Hessian frontier after consuming both planar quadratic
competitors through the existing packet machinery. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredHessianFrontier_with_packet_or_wSquare
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedBlockerExactFourBlockSchurData B ∨
      Nonempty (ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K)) ∨
      (HasFirstExactSmithExponentLongitudinalDeparture
          (polynomialFamilySpecialFiber B.aligned.endpoint.rightRecenteredFamily)
          B.exponent ∧
        (IsPureLongitudinalSmithPattern B.exponent ∨
          Nonempty
            (AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
              (K := K) B) ∨
          ({ b := 0, c := 0, d := 2 } : SmithSupportExponent) ∈
            smithProjectedSupport (1 : Fin 4) 2 3
              (longitudinalRightRecenterHom
                (K := K) B.aligned.endpoint.rawSpecialFiber))) := by
  rcases B.rightRecenteredHessianFrontier_with_allMinors hdefect with
    hschur | hzero | hres
  · exact Or.inl hschur
  · exact Or.inr (Or.inl hzero)
  · exact Or.inr (Or.inr
      ⟨hres.1,
        B.pureLongitudinal_or_packet_or_wSquare_of_allMinors hres.2⟩)

end

end HC4.Valuation
