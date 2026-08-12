import HC4.Valuation.AdaptiveAlignedSmithBlockerEndgame
import HC4.Valuation.AdaptiveAlignedSmithRecenteredHessianAllMinors
import HC4.Valuation.MovingCollisionRecentering
import Mathlib.Tactic

/-!
# Provenance-preserving closed blocker endgame

The local blocker geometry is already closed, but the compact endgame API
intentionally forgot two pieces of information which the final global
restart/terminal layer needs:

* a Schur/zero-Schur closing still lives on the honest right-recentered
  polynomial family and therefore carries an exact moving collision there;
* rigid quadratic packets arise only inside the all-`2 x 2`-minors-zero
  branch of the complete right-recentered special fibre.

This file retains those facts without changing any of the already-green
local classification.  In particular it does not introduce a new geometric
alternative.  It is purely a lossless interface for the final source-level
restart or terminal extraction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## Honest right-recentered collision source -/

/-- The right section after translating the actual endpoint family by its
original moving right section.  Since the original collision is `0 ~ b`, we
first reverse it to `b ~ 0`; after translation by `b` the collision is
`0 ~ -b`. -/
noncomputable def AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredRightSection
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    Fin 4 → Polynomial K :=
  polynomialSectionDifference E.movingSection
    (zeroPolynomialSection (K := K))

/-- The honest right-recentered family retains an exact moving gradient
collision. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily_exactCollision
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    HasPolynomialFamilyExactGradientCollision
      E.rightRecenteredFamily
      (zeroPolynomialSection (K := K))
      E.rightRecenteredRightSection := by
  have hswap :
      HasPolynomialFamilyExactGradientCollision
        E.family E.movingSection (zeroPolynomialSection (K := K)) := by
    intro i
    exact (E.exactCollision i).symm
  simpa [AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredFamily,
    AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredRightSection] using
    (polynomialFamilyExactGradientCollision_recenter
      (K := K) E.family E.movingSection
      (zeroPolynomialSection (K := K)) hswap)

/-- The surviving right section specializes to the negative marked axis. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredRightSection_specialPoint
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    polynomialSectionSpecialPoint E.rightRecenteredRightSection =
      (fun i => - coordinateAxisPoint (K := K) (0 : Fin 4) i) := by
  unfold AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredRightSection
  rw [polynomialSectionSpecialPoint_difference, E.sectionSpecial]
  funext i
  simp [zeroPolynomialSection, polynomialSectionSpecialPoint]

/-- The recentered collision remains genuinely between two distinct special
points. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredSpecialPoints_ne
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    (fun _ : Fin 4 => (0 : K)) ≠
      polynomialSectionSpecialPoint E.rightRecenteredRightSection := by
  rw [E.rightRecenteredRightSection_specialPoint]
  intro h
  have h0 := congrFun h (0 : Fin 4)
  simpa [coordinateAxisPoint] using h0

/-- The same exact collision descends to the right-recentered special fibre. -/
theorem AdaptiveAlignedSmithMinimalEndpoint.rightRecenteredSpecialFiber_exactCollision
    {degreeCap : ℕ}
    (E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap) :
    HasExactGradientCollision
      (polynomialFamilySpecialFiber E.rightRecenteredFamily)
      (fun _ : Fin 4 => (0 : K))
      (polynomialSectionSpecialPoint E.rightRecenteredRightSection) := by
  have h :=
    polynomialFamilyExactGradientCollision_specialFiber
      E.rightRecenteredFamily
      (zeroPolynomialSection (K := K))
      E.rightRecenteredRightSection
      E.rightRecenteredFamily_exactCollision
  have hzero :
      polynomialSectionSpecialPoint (zeroPolynomialSection (K := K)) =
        (fun _ : Fin 4 => (0 : K)) := by
    funext i
    simp [zeroPolynomialSection, polynomialSectionSpecialPoint]
  rw [hzero] at h
  exact h

/-- Source-level data retained by every blocker closing.  The family itself
is definitionally the honest right-recentered family used by the actual
Hessian four-block, so no matrix clock is being silently detached from its
polynomial source. -/
structure AdaptiveAlignedSmithBlockerRecenteredSourceData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) : Type _ where
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) B.aligned.endpoint.rightRecenteredFamily
      B.aligned.endpoint.defect
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      B.aligned.endpoint.rightRecenteredFamily
      (zeroPolynomialSection (K := K))
      B.aligned.endpoint.rightRecenteredRightSection
  specialPoints_ne :
    (fun _ : Fin 4 => (0 : K)) ≠
      polynomialSectionSpecialPoint
        B.aligned.endpoint.rightRecenteredRightSection

/-- Canonical source package for a blocker. -/
noncomputable def AdaptiveAlignedSmithBlockerEndpoint.recenteredSourceData
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) :
    AdaptiveAlignedSmithBlockerRecenteredSourceData B where
  hessianDefect := B.aligned.endpoint.rightRecenteredFamily_hessianDefect
  exactCollision := B.aligned.endpoint.rightRecenteredFamily_exactCollision
  specialPoints_ne := B.aligned.endpoint.rightRecenteredSpecialPoints_ne

/-! ## Provenance-preserving endgame -/

/-- Closed blocker outcome with the source/all-minors provenance needed by
later source-level restart or terminal extraction.  There is still no opaque
geometric constructor. -/
inductive AdaptiveAlignedSmithBlockerEndgameWithProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (complexity : ℕ) : Prop

  | certifiedStrictSuccessor
      (h : HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor RR B)

  | rankTwoRepair
      (h : RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity))

  | schurClosing
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B)

  | zeroSchurClosing
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z)

  | planarRigidPacket
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigidPacket
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- Planar packets arising from the all-minors branch keep that full-fibre
certificate when they are rigid. -/
theorem AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint.toBlockerEndgameWithProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithBlockerEndgameWithProvenance RR B complexity := by
  rcases P.localOutcome complexity with hrigid | ⟨_hesc, hprogress⟩
  · exact .planarRigidPacket hall P hrigid
  · exact .rankTwoRepair hprogress

/-- The `w^2` packet keeps the same full-fibre all-minors provenance. -/
theorem AdaptiveAlignedSmithWSquarePacketEndpoint.toBlockerEndgameWithProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    (hall :
      ∀ rho : Equiv.Perm (Fin 4),
        (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
          rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithBlockerEndgameWithProvenance RR B complexity := by
  rcases P.localOutcome complexity with hrigid | ⟨_hesc, hprogress⟩
  · exact .wSquareRigidPacket hall P hrigid
  · exact .rankTwoRepair hprogress

/-- **Lossless closed blocker endgame.**

This is the same exhaustive local theorem as `AdaptiveAlignedSmithBlockerEndpoint.endgame`,
but it deliberately retains the exact recentered collision source on closing
branches and the complete all-minors certificate on rigid packet branches. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.endgameWithProvenance
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (complexity : ℕ)
    (hdefect : 0 < B.aligned.endpoint.defect) :
    AdaptiveAlignedSmithBlockerEndgameWithProvenance RR B complexity := by
  rcases B.rightRecenteredHessianFrontier_with_allMinors hdefect with
    hschur | hzero | hres

  · rcases
        B.rankTwoProgress_or_closing_of_exactFourBlock
          (complexity := complexity) hschur with
      hprogress | hclosing
    · rcases hprogress with ⟨_S, hrepair, _hoffdiag, _hmeasure⟩
      exact .rankTwoRepair hrepair
    · exact .schurClosing B.recenteredSourceData hclosing

  · rcases hzero with ⟨Z⟩
    rcases Z.rankTwoProgress_or_closing complexity with
      hprogress | hclosing
    · exact .rankTwoRepair hprogress
    · exact .zeroSchurClosing B.recenteredSourceData Z hclosing

  · have hall := hres.2
    rcases B.pureLongitudinal_or_quadraticPacket_of_allMinors hall with
      hpure | hplanar | hw

    · rcases
          B.pureLongitudinal_transverseFree_or_quadraticPacket
            hpure hall with
        hfree | hplanar' | hw'
      · exact .certifiedStrictSuccessor
          (B.certifiedStrictSuccessor_of_transverseFree RR hfree)
      · rcases hplanar' with ⟨P⟩
        exact P.toBlockerEndgameWithProvenance RR hall complexity
      · rcases hw' with ⟨P⟩
        exact P.toBlockerEndgameWithProvenance RR hall complexity

    · rcases hplanar with ⟨P⟩
      exact P.toBlockerEndgameWithProvenance RR hall complexity

    · rcases hw with ⟨P⟩
      exact P.toBlockerEndgameWithProvenance RR hall complexity

/-- Forgetting the extra provenance recovers the already-green compact
blocker endgame.  This compatibility theorem lets later assembly migrate one
interface at a time. -/
theorem AdaptiveAlignedSmithBlockerEndgameWithProvenance.toEndgame
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    {complexity : ℕ}
    (h : AdaptiveAlignedSmithBlockerEndgameWithProvenance RR B complexity) :
    AdaptiveAlignedSmithBlockerEndgameOutcome RR B complexity := by
  rcases h with
    hstrict | hrepair | ⟨_source, hclose⟩ | ⟨_source, Z, hclose⟩ |
    ⟨_hall, P, hrigid⟩ | ⟨_hall, P, hrigid⟩
  · exact .certifiedStrictSuccessor hstrict
  · exact .rankTwoRepair hrepair
  · exact .schurClosing hclose
  · exact .zeroSchurClosing Z hclose
  · exact .planarRigidPacket P hrigid
  · exact .wSquareRigidPacket P hrigid

end

end HC4.Valuation
