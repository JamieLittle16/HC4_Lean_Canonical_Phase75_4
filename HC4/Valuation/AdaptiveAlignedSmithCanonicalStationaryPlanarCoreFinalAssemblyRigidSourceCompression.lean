import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyPostClosingCarrier
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape

/-!
# Final assembly A17.3A: source-complete rigid compression

After A17.2B only three local tags remain: the source-ready zero-Schur branch
and two rigid packet branches.  The planar and `w^2` rigid packets differ only
in the concrete persistent packet which witnessed the rank-one obstruction;
the source-facing data used by the final elimination is identical:

* one common scale-sound stationary blocker;
* the exact terminal source packet (zero integral transverse slopes plus the
  first same-Smith-exponent longitudinal departure);
* the complete all-`2 x 2`-minors-zero identity on the honest right-recentered
  special fibre;
* one actual rigid persistent packet.

This file packages those two rigid constructors into one source-complete
object and exposes the raw polynomial Hessian-minor identity directly.  It
also records the mixed-degree pair and all three positive transverse support
witnesses on the same literal special fibre.  No residual is declared
progress here: the purpose is to make the next theorem a single algebraic
eliminator rather than two packet-specific proofs.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The only packet-specific information retained by the final rigid
obstruction.  Both constructors carry a genuine rigid rank-one packet. -/
inductive AdaptiveAlignedSmithCanonicalRigidPacketWitness
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop
  | planar
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)
  | wSquare
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint
        (K := K) S.blocker)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- Source-complete form of the two rigid terminal constructors.

The `source` field is intentionally stored inside the object rather than
reconstructed from `S`: this certifies that the all-minors identity and the
first longitudinal departure used by the next argument belong to the same
terminal episode. -/
structure AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop where
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket S
  hall :
    ∀ rho : Equiv.Perm (Fin 4),
      (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
        rho S.blocker.aligned.endpoint).AllTwoByTwoMinorsZero
  packet : AdaptiveAlignedSmithCanonicalRigidPacketWitness S

namespace AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction

/-- The all-minors chart certificate is exactly the raw Hessian-minor
identity on the honest right-recentered special fibre. -/
theorem raw_allMinors
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S) :
    let G := longitudinalRightRecenterHom
      (K := K) S.blocker.aligned.endpoint.rawSpecialFiber
    ∀ i j k l : Fin 4,
      HC4.Polynomial.hessian G i j * HC4.Polynomial.hessian G k l -
        HC4.Polynomial.hessian G i l * HC4.Polynomial.hessian G k j = 0 := by
  exact rightRecentered_hessian_allMinors_raw S.blocker R.hall

/-- The rigid obstruction still has two actual occupied source monomials at
one transverse Smith exponent and distinct longitudinal levels. -/
theorem support_pair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S) :
    ∃ n q : ℕ,
      0 < q ∧
      ((smithTransverseExponent
          S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons n) ∈
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
      ((smithTransverseExponent
          S.blocker.exponent.b S.blocker.exponent.c S.blocker.exponent.d).cons (n + q)) ∈
        (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support :=
  R.source.support_pair

/-- The same literal special fibre is genuinely mixed in ordinary degree. -/
theorem mixedDegree_pair
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S) :
    ∃ d₀ d₁ : Fin 4 →₀ ℕ,
      d₀ ∈ (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
      d₁ ∈ (polynomialFamilySpecialFiber
        S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
      HC4.Polynomial.ordinaryDegree4 d₀ ≠
        HC4.Polynomial.ordinaryDegree4 d₁ := by
  refine ⟨S.mixed.d₀, S.mixed.d₁, ?_, ?_, S.mixed.degree_ne⟩
  · rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
    have h := S.mixed.d₀_mem
    rw [S.mixed_eq] at h
    exact h
  · rw [S.blocker.aligned.endpoint.rightRecenteredFamily_specialFiber]
    have h := S.mixed.d₁_mem
    rw [S.mixed_eq] at h
    exact h

/-- Every transverse coordinate occurs on that same special fibre. -/
theorem transverse_witnesses
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S) :
    (∃ d : Fin 4 →₀ ℕ,
        d ∈ (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
        0 < d (1 : Fin 4)) ∧
    (∃ d : Fin 4 →₀ ℕ,
        d ∈ (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
        0 < d (2 : Fin 4)) ∧
    (∃ d : Fin 4 →₀ ℕ,
        d ∈ (polynomialFamilySpecialFiber
          S.blocker.aligned.endpoint.rightRecenteredFamily).support ∧
        0 < d (3 : Fin 4)) :=
  S.specialFiber_witnesses

/-- All three maximal integral transverse slopes are already zero on the
rigid source normal form. -/
theorem integralZero
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s}
    (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S) :
    AdaptiveAlignedSmithScaleSoundAllTransverseIntegralZero S :=
  R.source.integralZero

end AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction

/-- A17.3A terminal geometry.  The two packet-specific rigid constructors are
now one source-complete obstruction. -/
inductive AdaptiveAlignedSmithCanonicalRigidCompressedTerminalGeometry
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (S : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s) : Prop
  | zeroSchurSourceReady
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier S.blocker)
      (source : AdaptiveAlignedSmithZeroSchurScaleSoundSourceData S.blocker C)
  | rigid
      (R : AdaptiveAlignedSmithCanonicalSourceCompleteRigidObstruction S)

/-- Local problem after rigid source compression. -/
structure AdaptiveAlignedSmithCanonicalRigidCompressedTerminalLocalProblem
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  stationary : AdaptiveAlignedSmithCanonicalScaleSoundStationaryBlocker s
  clock_eq :
    stationary.blocker.aligned.endpoint.defect =
      alignedSmithRamificationIndex * s.rawDefect
  clock_pos : 0 < stationary.blocker.aligned.endpoint.defect
  source : AdaptiveAlignedSmithCanonicalTerminalSourcePacket stationary
  geometry : AdaptiveAlignedSmithCanonicalRigidCompressedTerminalGeometry stationary

end

end HC4.Valuation
