import HC4.Newton.RankOnePacketExactCollision
import HC4.Newton.RankOneRepairProgress
import HC4.Newton.GeneralFourBlockSchur
import HC4.Newton.TerminalActualHessian
import Mathlib.Tactic

/-!
# Evaluated Hessian charts for a rigid persistent Smith packet

A rigid persistent packet has the exact algebraic form

    x^(D-2) * (A y^2 + B y z + C z^2)

and discriminant `B^2 - 4*A*C = 0`.

For the restart argument we do not need a polynomially invertible active
minor on the whole spatial affine space.  It is enough to evaluate the
parameter-family Hessian at one fixed spatial point: the Hessian determinant
clock is spatially constant, so spatial evaluation preserves it exactly.

This file supplies the scalar special-fibre calculation needed for that
move.  When `3 ≤ D`, put `m = D-2`, so `m > 0`.

* In the left-pivot chart evaluate at `(x,y,z,w)=(1,1,0,0)` and take
  `(x,y)` as the active coordinates.
* In the right-axis chart evaluate at `(1,0,1,0)` and take `(x,z)` as the
  active coordinates.

In either chart the active determinant is

    -2 * pivot^2 * m * (m+1),

hence is nonzero in characteristic zero.  The denominator-cleared Schur
block is exactly zero.  In the left chart its only potentially nonzero
entry is a scalar multiple of `B^2 - 4*A*C`; in the right chart the pivot
conditions force `A=B=0` directly.
-/

namespace HC4.Newton

noncomputable section

variable {K : Type*} [Field K]

/-- The scalar Hessian block used in the left rigid-packet chart. -/
noncomputable def rigidPacketLeftHessianBlock
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    GeneralFourBlock K :=
  let pt := rankOnePacketTransversePoint
    (0 : Fin 4) 1 2 (1 : K) 0
  {
    a := mvHessianComponentAt pt F 0 0
    b := mvHessianComponentAt pt F 0 1
    d := mvHessianComponentAt pt F 1 1
    p := mvHessianComponentAt pt F 0 2
    q := mvHessianComponentAt pt F 0 3
    r := mvHessianComponentAt pt F 1 2
    s := mvHessianComponentAt pt F 1 3
    x := mvHessianComponentAt pt F 2 2
    y := mvHessianComponentAt pt F 2 3
    z := mvHessianComponentAt pt F 3 3
  }

/-- The scalar Hessian block used in the right-axis rigid-packet chart.
The active coordinates are `(x,z)` and the complementary coordinates are
`(y,w)`. -/
noncomputable def rigidPacketRightHessianBlock
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K) :
    GeneralFourBlock K :=
  let pt := rankOnePacketTransversePoint
    (0 : Fin 4) 1 2 (0 : K) 1
  {
    a := mvHessianComponentAt pt F 0 0
    b := mvHessianComponentAt pt F 0 2
    d := mvHessianComponentAt pt F 2 2
    p := mvHessianComponentAt pt F 0 1
    q := mvHessianComponentAt pt F 0 3
    r := mvHessianComponentAt pt F 2 1
    s := mvHessianComponentAt pt F 2 3
    x := mvHessianComponentAt pt F 1 1
    y := mvHessianComponentAt pt F 1 3
    z := mvHessianComponentAt pt F 3 3
  }

private theorem fin4_distinct_01 : (0 : Fin 4) ≠ 1 := by decide
private theorem fin4_distinct_02 : (0 : Fin 4) ≠ 2 := by decide
private theorem fin4_distinct_12 : (1 : Fin 4) ≠ 2 := by decide

/-- Directed normalization for the numeral polynomial `2`.  Keep this out of
the global simp set: reversing `C_eq_coe_nat` inside `simp` loops with
`map_natCast` in the pinned mathlib. -/
private theorem pderiv_two_zero
    (i : Fin 4) :
    MvPolynomial.pderiv i (2 : MvPolynomial (Fin 4) K) = 0 := by
  have htwo : (2 : MvPolynomial (Fin 4) K) = 1 + 1 := by
    norm_num
  rw [htwo]
  simp only [map_add, MvPolynomial.pderiv_one, add_zero]

/-- Explicit active determinant in the left chart. -/
theorem rigidPacketLeftHessianBlock_activeDet
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hpacket :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 1 2 D F)
    (hD : 3 ≤ D) :
    (rigidPacketLeftHessianBlock D F).activeDet =
      -2 * (rankOnePacketCoeffYY (0 : Fin 4) 1 D F) ^ 2 *
        (((D - 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) := by
  have hm : 1 ≤ D - 2 := by omega
  have hmodel :=
    rankOnePersistentPacket_eq_algebraicModel
      fin4_distinct_01 fin4_distinct_02 fin4_distinct_12 hpacket
  calc
    (rigidPacketLeftHessianBlock D F).activeDet =
        (rigidPacketLeftHessianBlock D
          (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).activeDet :=
      congrArg (fun G => (rigidPacketLeftHessianBlock D G).activeDet) hmodel
    _ = -2 * (rankOnePacketCoeffYY (0 : Fin 4) 1 D F) ^ 2 *
          (((D - 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) := by
      unfold rigidPacketLeftHessianBlock GeneralFourBlock.activeDet
        mvHessianComponentAt rankOnePacketAlgebraicModel
      simp [rankOnePacketTransversePoint, Nat.cast_sub hm, pderiv_two_zero]
      ring_nf

/-- In the left chart the only potentially nonzero cleared Schur entry is
exactly a multiple of the packet discriminant. -/
theorem rigidPacketLeftHessianBlock_schurA
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hpacket :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 1 2 D F)
    (hD : 3 ≤ D) :
    (rigidPacketLeftHessianBlock D F).schurA =
      (((D - 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) *
        rankOnePacketCoeffYY (0 : Fin 4) 1 D F *
        rankOnePacketDiscriminant (0 : Fin 4) 1 2 D F := by
  have hm : 1 ≤ D - 2 := by omega
  have hmodel :=
    rankOnePersistentPacket_eq_algebraicModel
      fin4_distinct_01 fin4_distinct_02 fin4_distinct_12 hpacket
  calc
    (rigidPacketLeftHessianBlock D F).schurA =
        (rigidPacketLeftHessianBlock D
          (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).schurA :=
      congrArg (fun G => (rigidPacketLeftHessianBlock D G).schurA) hmodel
    _ = (((D - 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) *
          rankOnePacketCoeffYY (0 : Fin 4) 1 D F *
          rankOnePacketDiscriminant (0 : Fin 4) 1 2 D F := by
      unfold rigidPacketLeftHessianBlock GeneralFourBlock.schurA
        GeneralFourBlock.activeDet mvHessianComponentAt
        rankOnePacketAlgebraicModel rankOnePacketDiscriminant
      simp [rankOnePacketTransversePoint, Nat.cast_sub hm, pderiv_two_zero]
      ring_nf

/-- The fourth coordinate is absent from a persistent packet, so the left
chart's cleared off-diagonal Schur entry vanishes. -/
theorem rigidPacketLeftHessianBlock_schurB
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hpacket :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 1 2 D F) :
    (rigidPacketLeftHessianBlock D F).schurB = 0 := by
  have hmodel :=
    rankOnePersistentPacket_eq_algebraicModel
      fin4_distinct_01 fin4_distinct_02 fin4_distinct_12 hpacket
  calc
    (rigidPacketLeftHessianBlock D F).schurB =
        (rigidPacketLeftHessianBlock D
          (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).schurB :=
      congrArg (fun G => (rigidPacketLeftHessianBlock D G).schurB) hmodel
    _ = 0 := by
      unfold rigidPacketLeftHessianBlock GeneralFourBlock.schurB
        GeneralFourBlock.activeDet mvHessianComponentAt
        rankOnePacketAlgebraicModel
      simp [rankOnePacketTransversePoint]

/-- The fourth-coordinate diagonal Schur entry also vanishes. -/
theorem rigidPacketLeftHessianBlock_schurC
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hpacket :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 1 2 D F) :
    (rigidPacketLeftHessianBlock D F).schurC = 0 := by
  have hmodel :=
    rankOnePersistentPacket_eq_algebraicModel
      fin4_distinct_01 fin4_distinct_02 fin4_distinct_12 hpacket
  calc
    (rigidPacketLeftHessianBlock D F).schurC =
        (rigidPacketLeftHessianBlock D
          (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).schurC :=
      congrArg (fun G => (rigidPacketLeftHessianBlock D G).schurC) hmodel
    _ = 0 := by
      unfold rigidPacketLeftHessianBlock GeneralFourBlock.schurC
        GeneralFourBlock.activeDet mvHessianComponentAt
        rankOnePacketAlgebraicModel
      simp [rankOnePacketTransversePoint]

/-- The left rigid pivot therefore gives an invertible active scalar minor
and zero special Schur block. -/
theorem rigidPacket_left_zeroSchurChart
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hpacket :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 1 2 D F)
    (hrigid :
      HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D F)
    (hleft :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D F).LeftPivot)
    (hD : 3 ≤ D) :
    (rigidPacketLeftHessianBlock D F).activeDet ≠ 0 ∧
      (rigidPacketLeftHessianBlock D F).schurA = 0 ∧
      (rigidPacketLeftHessianBlock D F).schurB = 0 ∧
      (rigidPacketLeftHessianBlock D F).schurC = 0 := by
  let A := rankOnePacketCoeffYY (0 : Fin 4) 1 D F
  have hA : A ≠ 0 := by
    intro hzero
    apply hleft.1
    simp [rankOnePacketQuadraticBlock, A, hzero]
  have hm0 : D - 2 ≠ 0 := by omega
  have hm10 : (D - 2) + 1 ≠ 0 := by omega
  have hcastm : (((D - 2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast hm0
  have hcastm1 : ((((D - 2) + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast hm10
  constructor
  · rw [rigidPacketLeftHessianBlock_activeDet hpacket hD]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hA)) hcastm)
      hcastm1
  constructor
  · rw [rigidPacketLeftHessianBlock_schurA hpacket hD]
    rw [hrigid.1]
    simp
  constructor
  · exact rigidPacketLeftHessianBlock_schurB hpacket
  · exact rigidPacketLeftHessianBlock_schurC hpacket

/-- Explicit active determinant in the right-axis chart. -/
theorem rigidPacketRightHessianBlock_activeDet
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hpacket :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 1 2 D F)
    (hD : 3 ≤ D) :
    (rigidPacketRightHessianBlock D F).activeDet =
      -2 * (rankOnePacketCoeffZZ (0 : Fin 4) 2 D F) ^ 2 *
        (((D - 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) := by
  have hm : 1 ≤ D - 2 := by omega
  have hmodel :=
    rankOnePersistentPacket_eq_algebraicModel
      fin4_distinct_01 fin4_distinct_02 fin4_distinct_12 hpacket
  calc
    (rigidPacketRightHessianBlock D F).activeDet =
        (rigidPacketRightHessianBlock D
          (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).activeDet :=
      congrArg (fun G => (rigidPacketRightHessianBlock D G).activeDet) hmodel
    _ = -2 * (rankOnePacketCoeffZZ (0 : Fin 4) 2 D F) ^ 2 *
          (((D - 2 : ℕ) : K)) * ((((D - 2) + 1 : ℕ) : K)) := by
      unfold rigidPacketRightHessianBlock GeneralFourBlock.activeDet
        mvHessianComponentAt rankOnePacketAlgebraicModel
      simp [rankOnePacketTransversePoint, Nat.cast_sub hm, pderiv_two_zero]
      ring_nf

/-- A right-axis pivot forces the scalar packet coefficients `A=B=0`. -/
theorem rigidPacket_rightAxis_coefficients
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hright :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D F).RightAxisPivot) :
    rankOnePacketCoeffYY (0 : Fin 4) 1 D F = 0 ∧
      rankOnePacketCoeffYZ (0 : Fin 4) 1 2 D F = 0 ∧
      rankOnePacketCoeffZZ (0 : Fin 4) 2 D F ≠ 0 := by
  have hfour : (4 : K) ≠ 0 := by norm_num
  have htwo : (2 : K) ≠ 0 := by norm_num
  rcases hright with ⟨ha, hb, hc⟩
  constructor
  · change 4 * rankOnePacketCoeffYY (0 : Fin 4) 1 D F = 0 at ha
    exact (mul_eq_zero.mp ha).resolve_left hfour
  constructor
  · change 2 * rankOnePacketCoeffYZ (0 : Fin 4) 1 2 D F = 0 at hb
    exact (mul_eq_zero.mp hb).resolve_left htwo
  · intro hC
    apply hc
    change 4 * rankOnePacketCoeffZZ (0 : Fin 4) 2 D F = 0
    rw [hC]
    simp

/-- The right-axis rigid chart also has zero special Schur block. -/
theorem rigidPacket_right_zeroSchurChart
    [CharZero K]
    {D : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hpacket :
      HasRankOnePersistentPacketSupport
        (0 : Fin 4) 1 2 D F)
    (hright :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D F).RightAxisPivot)
    (hD : 3 ≤ D) :
    (rigidPacketRightHessianBlock D F).activeDet ≠ 0 ∧
      (rigidPacketRightHessianBlock D F).schurA = 0 ∧
      (rigidPacketRightHessianBlock D F).schurB = 0 ∧
      (rigidPacketRightHessianBlock D F).schurC = 0 := by
  rcases rigidPacket_rightAxis_coefficients (K := K) hright with
    ⟨hA, hB, hC⟩
  have hm0 : D - 2 ≠ 0 := by omega
  have hm10 : (D - 2) + 1 ≠ 0 := by omega
  have hcastm : (((D - 2 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast hm0
  have hcastm1 : ((((D - 2) + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast hm10
  constructor
  · rw [rigidPacketRightHessianBlock_activeDet hpacket hD]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC)) hcastm)
      hcastm1
  have hmodel :=
    rankOnePersistentPacket_eq_algebraicModel
      fin4_distinct_01 fin4_distinct_02 fin4_distinct_12 hpacket
  constructor
  · calc
      (rigidPacketRightHessianBlock D F).schurA =
          (rigidPacketRightHessianBlock D
            (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).schurA :=
        congrArg (fun G => (rigidPacketRightHessianBlock D G).schurA) hmodel
      _ = 0 := by
        unfold rigidPacketRightHessianBlock GeneralFourBlock.schurA
          GeneralFourBlock.activeDet mvHessianComponentAt
          rankOnePacketAlgebraicModel
        simp [rankOnePacketTransversePoint, hA, hB]
  constructor
  · calc
      (rigidPacketRightHessianBlock D F).schurB =
          (rigidPacketRightHessianBlock D
            (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).schurB :=
        congrArg (fun G => (rigidPacketRightHessianBlock D G).schurB) hmodel
      _ = 0 := by
        unfold rigidPacketRightHessianBlock GeneralFourBlock.schurB
          GeneralFourBlock.activeDet mvHessianComponentAt
          rankOnePacketAlgebraicModel
        simp [rankOnePacketTransversePoint, hA, hB]
  · calc
      (rigidPacketRightHessianBlock D F).schurC =
          (rigidPacketRightHessianBlock D
            (rankOnePacketAlgebraicModel (0 : Fin 4) 1 2 D F)).schurC :=
        congrArg (fun G => (rigidPacketRightHessianBlock D G).schurC) hmodel
      _ = 0 := by
        unfold rigidPacketRightHessianBlock GeneralFourBlock.schurC
          GeneralFourBlock.activeDet mvHessianComponentAt
          rankOnePacketAlgebraicModel
        simp [rankOnePacketTransversePoint, hA, hB]

end

end HC4.Newton
