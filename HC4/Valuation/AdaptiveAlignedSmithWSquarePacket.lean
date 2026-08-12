import HC4.Valuation.AdaptiveAlignedSmithQuadraticCompetitorPacket
import HC4.Newton.RankOneRepairProgress
import Mathlib.Tactic

/-!
# Positive-grade w-square competitor to a persistent packet

The remaining quadratic competitor from the rank-at-most-one blocker Hessian
is the projected exponent

    (b,c,d) = (0,0,2).

There is no need to run a new Smith tilt or to rename the ambient polynomial.
Projected-support membership is realised by an actual monomial of the
right-recentered special fibre.  Such a monomial has the form

    c * x^a * w^2.

Taking that single monomial as a packet and choosing the transverse packet
axes to be `(w,z)` gives exactly the existing persistent rank-one support
pattern

    x^(D-2) * q(w,z),      q(w,z) = c w^2.

Thus the `w^2` competitor enters the same rigid/rank-two repair classifier as
the two planar quadratic competitors.  No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A concrete one-monomial persistent packet extracted from an actual
`w^2` projected-support competitor in the right-recentered blocker fibre. -/
structure AdaptiveAlignedSmithWSquarePacketEndpoint
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap) where
  sourceExponent : Fin 4 →₀ ℕ
  sourceCoeff_ne :
    MvPolynomial.coeff sourceExponent
      (longitudinalRightRecenterHom
        (K := K) B.aligned.endpoint.rawSpecialFiber) ≠ 0
  source_y_zero : sourceExponent 1 = 0
  source_z_zero : sourceExponent 2 = 0
  source_w_two : sourceExponent 3 = 2
  degree : ℕ
  degree_eq :
    degree = HC4.Polynomial.ordinaryDegree4 sourceExponent
  packet : MvPolynomial (Fin 4) K
  packet_eq :
    packet =
      MvPolynomial.monomial sourceExponent
        (MvPolynomial.coeff sourceExponent
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber))
  packet_ne_zero : packet ≠ 0
  degree_ge_two : 2 ≤ degree
  persistent :
    HasRankOnePersistentPacketSupport
      (0 : Fin 4) 3 2 degree packet

/-- Any actual `w^2` projected-support competitor supplies a one-monomial
persistent packet on transverse axes `(w,z)`. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.wSquarePacket
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap)
    (hw :
      ({ b := 0, c := 0, d := 2 } : SmithSupportExponent) ∈
        smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)) :
    Nonempty (AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B) := by
  let G := longitudinalRightRecenterHom
    (K := K) B.aligned.endpoint.rawSpecialFiber
  rcases
      smithProjectedSupport_realised
        (1 : Fin 4) 2 3 G
        ({ b := 0, c := 0, d := 2 } : SmithSupportExponent) hw with
    ⟨d, hd, hproj⟩

  have hy : d 1 = 0 := by
    have h := congrArg SmithSupportExponent.b hproj
    simpa [smithSupportExponentOf] using h
  have hz : d 2 = 0 := by
    have h := congrArg SmithSupportExponent.c hproj
    simpa [smithSupportExponentOf] using h
  have hw2 : d 3 = 2 := by
    have h := congrArg SmithSupportExponent.d hproj
    simpa [smithSupportExponentOf] using h

  let D := HC4.Polynomial.ordinaryDegree4 d
  let c := MvPolynomial.coeff d G
  let Q : MvPolynomial (Fin 4) K := MvPolynomial.monomial d c

  have hc : c ≠ 0 := by
    simpa [c, G] using hd

  have hD : 2 ≤ D := by
    dsimp [D]
    simp only [HC4.Polynomial.ordinaryDegree4]
    omega

  have hx : d 0 = D - 2 := by
    dsimp [D]
    simp only [HC4.Polynomial.ordinaryDegree4]
    omega

  have hQne : Q ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun P : MvPolynomial (Fin 4) K => MvPolynomial.coeff d P) hzero
    simp [Q, c, hc] at hcoeff

  have hpersistent :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 3 2 D Q := by
    intro q hq
    have hqd : q = d := by
      by_contra hne
      have hne' : d ≠ q := Ne.symm hne
      simp [Q, hne, hne', hc] at hq
    subst q
    refine ⟨hx, ?_, ?_⟩
    · omega
    · intro t ht0 ht3 ht2
      fin_cases t <;> simp_all

  exact
    ⟨{
      sourceExponent := d
      sourceCoeff_ne := by simpa [G] using hd
      source_y_zero := hy
      source_z_zero := hz
      source_w_two := hw2
      degree := D
      degree_eq := rfl
      packet := Q
      packet_eq := rfl
      packet_ne_zero := hQne
      degree_ge_two := hD
      persistent := hpersistent
    }⟩

/-- Local algebraic outcome of the one-monomial `w^2` packet. -/
inductive AdaptiveAlignedSmithWSquarePacketLocalOutcome
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
    (complexity : ℕ) : Prop
  | rigid
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)
  | rankTwo
      (hesc : HasRankTwoPacketEscalation
        (0 : Fin 4) 3 2 P.degree P.packet)
      (hprogress :
        RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity))

/-- The existing rank-one packet classifier consumes the `w^2` packet
without any new geometric argument. -/
theorem AdaptiveAlignedSmithWSquarePacketEndpoint.localOutcome
    [CharZero K]
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
    (complexity : ℕ) :
    AdaptiveAlignedSmithWSquarePacketLocalOutcome P complexity := by
  rcases
      rankOnePersistentPacket_rigid_or_rankTwoProgress
        (complexity := complexity)
        (by decide : (0 : Fin 4) ≠ 3)
        (by decide : (0 : Fin 4) ≠ 2)
        (by decide : (3 : Fin 4) ≠ 2)
        P.persistent P.packet_ne_zero with
    hrigid | hrankTwo
  · exact .rigid hrigid
  · exact .rankTwo hrankTwo.1 hrankTwo.2

/-- The all-minors exceptional branch now has only two genuine outputs:
the pure-longitudinal blocker, or an actual persistent packet (planar or
`w^2`). -/
theorem AdaptiveAlignedSmithBlockerEndpoint.pureLongitudinal_or_quadraticPacket_of_allMinors
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
      Nonempty
        (AdaptiveAlignedSmithWSquarePacketEndpoint
          (K := K) B) := by
  rcases B.pureLongitudinal_or_packet_or_wSquare_of_allMinors hall with
    hpure | hpacket | hw
  · exact Or.inl hpure
  · exact Or.inr (Or.inl hpacket)
  · exact Or.inr (Or.inr (B.wSquarePacket hw))

/-- Dispatcher-facing Hessian frontier after consuming *all three* quadratic
competitors into persistent packet data.  The only exceptional nonpacket
all-minors branch left is pure longitudinal. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.rightRecenteredHessianFrontier_with_quadraticPackets
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
          Nonempty
            (AdaptiveAlignedSmithWSquarePacketEndpoint
              (K := K) B))) := by
  rcases B.rightRecenteredHessianFrontier_with_allMinors hdefect with
    hschur | hzero | hres
  · exact Or.inl hschur
  · exact Or.inr (Or.inl hzero)
  · exact Or.inr (Or.inr
      ⟨hres.1,
        B.pureLongitudinal_or_quadraticPacket_of_allMinors hres.2⟩)

end

end HC4.Valuation
