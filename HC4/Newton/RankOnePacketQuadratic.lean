import HC4.Newton.RankOnePersistentPacket
import Mathlib.Tactic

/-!
# The binary quadratic carried by a rank-one persistent packet

Phase 92.1 reduces a persistent packet

    x^(D-2) * q(y,z)

to exactly three coefficients, belonging to

    x^(D-2) y^2,
    x^(D-2) y z,
    x^(D-2) z^2.

Write these coefficients as `A,B,C`.  Then

    q(Y,Z) = A Y^2 + B Y Z + C Z^2.

To reuse the Phase 90/91 binary Schur machinery without introducing
division by `2`, we attach the denominator-cleared symmetric block

        [ 4A  2B ]
        [ 2B  4C ].

This is four times the usual symmetric matrix

        [ A    B/2 ]
        [ B/2  C   ],

so in characteristic zero it has exactly the same rank.  Its associated
quadratic form is literally `4*q`, and its determinant is

    -4 * (B^2 - 4AC).

Therefore:

* discriminant zero + nonzero packet gives a nonzero determinant-zero
  `BinarySchurBlock`, hence the square/pivot geometry already proved in
  Phase 91;
* discriminant nonzero gives a genuinely nondegenerate binary block.

This is the first formal re-entry interface from the rank-one persistent
packet into the already checked rank-two/rank-one binary machinery.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- The actual binary quadratic carried by the three persistent-packet
coefficients. -/
def rankOnePacketQuadratic
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (Y Z : K) : K :=
  rankOnePacketCoeffYY x y D F * Y * Y +
    rankOnePacketCoeffYZ x y z D F * Y * Z +
    rankOnePacketCoeffZZ x z D F * Z * Z

/-- Denominator-cleared symmetric block attached to the persistent binary
quadratic.  It is four times the conventional block with off-diagonal
entry `B/2`. -/
def rankOnePacketQuadraticBlock
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) :
    BinarySchurBlock K where
  a := 4 * rankOnePacketCoeffYY x y D F
  b := 2 * rankOnePacketCoeffYZ x y z D F
  c := 4 * rankOnePacketCoeffZZ x z D F

/-- Conventional discriminant `B^2 - 4AC` of the persistent binary
quadratic. -/
def rankOnePacketDiscriminant
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) : K :=
  rankOnePacketCoeffYZ x y z D F *
      rankOnePacketCoeffYZ x y z D F -
    4 *
      rankOnePacketCoeffYY x y D F *
      rankOnePacketCoeffZZ x z D F

/-- The persistent packet is nonzero exactly at the level needed here:
at least one of its three canonical coefficients is nonzero. -/
def RankOnePacketQuadraticNonzero
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  rankOnePacketCoeffYY x y D F ≠ 0 ∨
    rankOnePacketCoeffYZ x y z D F ≠ 0 ∨
    rankOnePacketCoeffZZ x z D F ≠ 0

/-- The cleared block quadratic is exactly four times the original
persistent binary quadratic. -/
theorem rankOnePacketQuadraticBlock_quadratic
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (Y Z : K) :
    (rankOnePacketQuadraticBlock x y z D F).quadratic Y Z =
      4 * rankOnePacketQuadratic x y z D F Y Z := by
  simp [rankOnePacketQuadraticBlock,
    BinarySchurBlock.quadratic, rankOnePacketQuadratic]
  ring

/-- Exact determinant/discriminant relation for the denominator-cleared
block. -/
theorem rankOnePacketQuadraticBlock_detCore
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) :
    (rankOnePacketQuadraticBlock x y z D F).detCore =
      - (4 * rankOnePacketDiscriminant x y z D F) := by
  simp [rankOnePacketQuadraticBlock,
    BinarySchurBlock.detCore, rankOnePacketDiscriminant]
  ring

/-- A nonzero persistent quadratic gives a nonzero cleared Schur block in
characteristic zero. -/
theorem rankOnePacketQuadraticBlock_nonzero
    [CharZero K]
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (hnz : RankOnePacketQuadraticNonzero x y z D F) :
    (rankOnePacketQuadraticBlock x y z D F).Nonzero := by
  have htwo : (2 : K) ≠ 0 := by
    norm_num
  have hfour : (4 : K) ≠ 0 := by
    norm_num
  rcases hnz with hA | hB | hC
  · left
    change
      4 * rankOnePacketCoeffYY x y D F ≠ 0
    exact mul_ne_zero hfour hA
  · right
    left
    change
      2 * rankOnePacketCoeffYZ x y z D F ≠ 0
    exact mul_ne_zero htwo hB
  · right
    right
    change
      4 * rankOnePacketCoeffZZ x z D F ≠ 0
    exact mul_ne_zero hfour hC

/-- In characteristic zero, the cleared block has determinant zero exactly
when the original binary quadratic has discriminant zero. -/
theorem rankOnePacketQuadraticBlock_detCore_eq_zero_iff
    [CharZero K]
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) :
    (rankOnePacketQuadraticBlock x y z D F).detCore = 0 ↔
      rankOnePacketDiscriminant x y z D F = 0 := by
  have hfour : (4 : K) ≠ 0 := by
    norm_num
  constructor
  · intro hdet
    have hrel :=
      rankOnePacketQuadraticBlock_detCore
        x y z D F
    rw [hdet] at hrel
    have hprod :
        (4 : K) * rankOnePacketDiscriminant x y z D F = 0 := by
      exact neg_eq_zero.mp hrel.symm
    exact (mul_eq_zero.mp hprod).resolve_left hfour
  · intro hdisc
    rw [rankOnePacketQuadraticBlock_detCore, hdisc]
    simp

/-- Discriminant-zero nonzero packets immediately inherit the explicit
square geometry of Phase 91. -/
theorem rankOnePacket_squareGeometry_of_discriminant_eq_zero
    [CharZero K]
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (hnz : RankOnePacketQuadraticNonzero x y z D F)
    (hdisc : rankOnePacketDiscriminant x y z D F = 0) :
    let q := rankOnePacketQuadraticBlock x y z D F
    (q.LeftPivot ∧
      (∀ Y Z : K,
        q.a * q.quadratic Y Z =
          (q.a * Y + q.b * Z) ^ 2)) ∨
    (q.RightAxisPivot ∧
      (∀ Y Z : K,
        q.quadratic Y Z = q.c * Z * Z)) := by
  dsimp
  exact
    BinarySchurBlock.squareGeometry_of_detCore_eq_zero
      (rankOnePacketQuadraticBlock x y z D F)
      ((rankOnePacketQuadraticBlock_detCore_eq_zero_iff
        x y z D F).2 hdisc)
      (rankOnePacketQuadraticBlock_nonzero
        x y z D F hnz)

/-- **Quadratic rank alternative for the first persistent packet.**
A nonzero packet either has discriminant zero and hence the already-checked
rank-one square geometry, or it has nonzero determinant and is genuinely
rank two in the transverse variables. -/
theorem rankOnePacket_discriminant_zero_or_nondegenerate
    [CharZero K]
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K)
    (hnz : RankOnePacketQuadraticNonzero x y z D F) :
    (rankOnePacketDiscriminant x y z D F = 0 ∧
      let q := rankOnePacketQuadraticBlock x y z D F
      q.LeftPivot ∨ q.RightAxisPivot) ∨
    (rankOnePacketDiscriminant x y z D F ≠ 0 ∧
      (rankOnePacketQuadraticBlock x y z D F).detCore ≠ 0) := by
  by_cases hdisc :
      rankOnePacketDiscriminant x y z D F = 0
  · left
    refine ⟨hdisc, ?_⟩
    dsimp
    exact
      BinarySchurBlock.pivot_of_detCore_eq_zero
        (rankOnePacketQuadraticBlock x y z D F)
        ((rankOnePacketQuadraticBlock_detCore_eq_zero_iff
          x y z D F).2 hdisc)
        (rankOnePacketQuadraticBlock_nonzero
          x y z D F hnz)
  · right
    refine ⟨hdisc, ?_⟩
    intro hdet
    exact hdisc
      ((rankOnePacketQuadraticBlock_detCore_eq_zero_iff
        x y z D F).1 hdet)

end

end HC4.Newton
