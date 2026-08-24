import HC4.Valuation.AdaptiveAlignedSmithWSquarePacket
import Mathlib.Tactic

/-!
# A18.4.100: actual axis competitor packets are rigid

The historical planar packet endpoint allows all three binary quadratic
patterns `(2,0)`, `(1,1)`, `(0,2)`.  The blocker all-minors argument is
stronger: the competitors it actually constructs are only the two axis
squares `(2,0,0)` and `(0,2,0)` (plus the separately handled `w^2` square).

For a singleton Smith subface at either planar axis square, the minimal
longitudinal degree component has no mixed `yz` coefficient and no opposite
axis-square coefficient.  Consequently its binary discriminant is zero.
The one-monomial `w^2` packet has the identical property on axes `(w,z)`.

Thus every quadratic packet genuinely produced by the blocker all-minors
argument is rigid; the abstract packet rank-two alternative is unreachable on
this producer.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The two planar competitors actually forced by the blocker Hessian. -/
def IsPlanarAxisSquareCompetitor (e : SmithSupportExponent) : Prop :=
  e = ({ b := 2, c := 0, d := 0 } : SmithSupportExponent) ∨
  e = ({ b := 0, c := 2, d := 0 } : SmithSupportExponent)

namespace AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint

/-- The mixed packet coefficient vanishes for an actual axis-square singleton
competitor. -/
theorem coeffYZ_eq_zero_of_axisSquare
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (haxis : IsPlanarAxisSquareCompetitor P.competitor) :
    rankOnePacketCoeffYZ (0 : Fin 4) 1 2 P.degree P.packet = 0 := by
  rw [P.provenance.packet_eq]
  unfold rankOnePacketCoeffYZ
  rw [coeff_smithSubfaceDegreeComponent]
  have hproj :
      smithSupportExponentOf (1 : Fin 4) 2 3
          (rankOnePacketYZ (0 : Fin 4) 1 2 P.degree) =
        ({ b := 1, c := 1, d := 0 } : SmithSupportExponent) := by
    ext <;> simp [smithSupportExponentOf, rankOnePacketYZ]
  rw [hproj]
  rcases haxis with haxis | haxis <;> rw [haxis] <;> simp

/-- If the actual competitor is `y^2`, the opposite `z^2` packet coefficient
vanishes. -/
theorem coeffZZ_eq_zero_of_ySquare
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (haxis : P.competitor =
      ({ b := 2, c := 0, d := 0 } : SmithSupportExponent)) :
    rankOnePacketCoeffZZ (0 : Fin 4) 2 P.degree P.packet = 0 := by
  rw [P.provenance.packet_eq]
  unfold rankOnePacketCoeffZZ
  rw [coeff_smithSubfaceDegreeComponent]
  have hproj :
      smithSupportExponentOf (1 : Fin 4) 2 3
          (rankOnePacketZZ (0 : Fin 4) 2 P.degree) =
        ({ b := 0, c := 2, d := 0 } : SmithSupportExponent) := by
    ext <;> simp [smithSupportExponentOf, rankOnePacketZZ]
  rw [hproj, haxis]
  simp

/-- If the actual competitor is `z^2`, the opposite `y^2` packet coefficient
vanishes. -/
theorem coeffYY_eq_zero_of_zSquare
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (haxis : P.competitor =
      ({ b := 0, c := 2, d := 0 } : SmithSupportExponent)) :
    rankOnePacketCoeffYY (0 : Fin 4) 1 P.degree P.packet = 0 := by
  rw [P.provenance.packet_eq]
  unfold rankOnePacketCoeffYY
  rw [coeff_smithSubfaceDegreeComponent]
  have hproj :
      smithSupportExponentOf (1 : Fin 4) 2 3
          (rankOnePacketYY (0 : Fin 4) 1 P.degree) =
        ({ b := 2, c := 0, d := 0 } : SmithSupportExponent) := by
    ext <;> simp [smithSupportExponentOf, rankOnePacketYY]
  rw [hproj, haxis]
  simp

/-- **Axis-square singleton packets have zero discriminant.** -/
theorem discriminant_eq_zero_of_axisSquare
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (haxis : IsPlanarAxisSquareCompetitor P.competitor) :
    rankOnePacketDiscriminant
      (0 : Fin 4) 1 2 P.degree P.packet = 0 := by
  have hYZ := P.coeffYZ_eq_zero_of_axisSquare haxis
  rcases haxis with hy | hz
  · have hZZ := P.coeffZZ_eq_zero_of_ySquare hy
    simp [rankOnePacketDiscriminant, hYZ, hZZ]
  · have hYY := P.coeffYY_eq_zero_of_zSquare hz
    simp [rankOnePacketDiscriminant, hYZ, hYY]

/-- Therefore every actual planar axis-square packet is already rigid. -/
theorem rigid_of_axisSquare
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
    (haxis : IsPlanarAxisSquareCompetitor P.competitor) :
    HasRigidRankOnePacket
      (0 : Fin 4) 1 2 P.degree P.packet := by
  have hnz :
      RankOnePacketQuadraticNonzero
        (0 : Fin 4) 1 2 P.degree P.packet :=
    rankOnePacketQuadraticNonzero_of_polynomial_ne_zero
      (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (1 : Fin 4) ≠ 2)
      P.persistent P.provenance.packet_ne_zero
  have hdisc := P.discriminant_eq_zero_of_axisSquare haxis
  exact ⟨hdisc,
    rankOnePacket_squareGeometry_of_discriminant_eq_zero
      (0 : Fin 4) 1 2 P.degree P.packet hnz hdisc⟩

end AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint

namespace AdaptiveAlignedSmithWSquarePacketEndpoint

/-- The `w^2` packet is literally one monomial, so its mixed `(w,z)` and
opposite `z^2` coefficients vanish. -/
theorem discriminant_eq_zero
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B) :
    rankOnePacketDiscriminant
      (0 : Fin 4) 3 2 P.degree P.packet = 0 := by
  rw [P.packet_eq]
  unfold rankOnePacketDiscriminant rankOnePacketCoeffYY
    rankOnePacketCoeffYZ rankOnePacketCoeffZZ
  have hYZ :
      rankOnePacketYZ (0 : Fin 4) 3 2 P.degree ≠ P.sourceExponent := by
    intro h
    have hw := congrArg (fun d : Fin 4 →₀ ℕ => d 3) h
    simp [rankOnePacketYZ, P.source_w_two] at hw
  have hZZ :
      rankOnePacketZZ (0 : Fin 4) 2 P.degree ≠ P.sourceExponent := by
    intro h
    have hw := congrArg (fun d : Fin 4 →₀ ℕ => d 3) h
    simp [rankOnePacketZZ, P.source_w_two] at hw
  simp [hYZ, hZZ]

/-- Therefore the actual one-monomial `w^2` packet is rigid. -/
theorem rigid
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B) :
    HasRigidRankOnePacket
      (0 : Fin 4) 3 2 P.degree P.packet := by
  have hnz :
      RankOnePacketQuadraticNonzero
        (0 : Fin 4) 3 2 P.degree P.packet :=
    rankOnePacketQuadraticNonzero_of_polynomial_ne_zero
      (by decide : (0 : Fin 4) ≠ 3)
      (by decide : (0 : Fin 4) ≠ 2)
      (by decide : (3 : Fin 4) ≠ 2)
      P.persistent P.packet_ne_zero
  have hdisc := P.discriminant_eq_zero
  exact ⟨hdisc,
    rankOnePacket_squareGeometry_of_discriminant_eq_zero
      (0 : Fin 4) 3 2 P.degree P.packet hnz hdisc⟩

end AdaptiveAlignedSmithWSquarePacketEndpoint

end

end HC4.Valuation
