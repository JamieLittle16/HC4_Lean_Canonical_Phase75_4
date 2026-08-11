import HC4.Valuation.AdaptiveAlignedSmithRankTwoMatrix
import HC4.Valuation.AdaptiveRigidMatrixExposure
import HC4.Valuation.AdaptiveRankTwoMatrixExposure
import Mathlib.Tactic

/-!
# Aligned rank-two matrix exposure to exact zero-Schur data

The aligned surviving-wall programme now reaches an actual
`AdaptiveRankTwoMatrixExposure`.  The current repository already contains
both remaining local ingredients:

* packet isolation for the exceptional cubic degree `D = 3`, using
  ramification `R = 3`;
* packet isolation for every `D >= 4`.

It also contains the generic normalization-preserving matrix reindexing and
the constructor
`rankTwoExactZeroSchurData_of_packetIsolation`.

This file only joins those existing theorems.

To keep the interface completely honest, positivity of the *exposed*
determinant clock is taken explicitly here.  A separate already-developed
quadratic-special-fibre theorem can discharge that hypothesis afterwards.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The constant packet Hessian matrix at the canonical longitudinal axis
point used by the rank-two isolation theorems. -/
noncomputable def
    AdaptiveAlignedSmithRankTwoMatrixEndpoint.packetAxisHessian
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2) :
    Matrix (Fin 4) (Fin 4) K :=
  fun i j =>
    mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ : Fin 4 => (0 : K)))
      P.packet i j

/-- After the canonical `(1,2 | 0,3)` reindexing, the packet-axis Hessian is
exactly the four-block expected by the zero-Schur constructor. -/
theorem
    AdaptiveAlignedSmithRankTwoMatrixEndpoint.packetAxisHessian_fourBlock
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2) :
    GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm
          M.packetAxisHessian) =
      rankTwoPacketAxisFourBlock P.degree P.packet := by
  simpa [AdaptiveAlignedSmithRankTwoMatrixEndpoint.packetAxisHessian] using
    (rankTwoPacket_reindexedAxisHessian_eq_fourBlock
      R2.continuation.persistentPacket)

/-- **Actual aligned rank-two matrix exposure -> exact zero-Schur data.**

For `D = 3` we reuse the exceptional cubic packet-isolation theorem with
`R = 3` and isolation order `n = 1`.

For `D >= 4` we choose

    R = 6 * (D - 2).

This is comfortably larger than the packet-isolation threshold
`2 * (D - 2)` and, once the exposed determinant defect is positive, makes
the zero-Schur clock inequality automatic.

No new Schur algebra occurs here. -/
noncomputable def
    AdaptiveAlignedSmithRankTwoMatrixEndpoint.toExactZeroSchur
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2)
    (hD : 3 ≤ P.degree)
    (hDelta : 0 < M.exposure.defect) :
    ExactZeroSchurFourBlockData K := by
  let point : Fin 4 → K := fun _ => 0
  let C : Matrix (Fin 4) (Fin 4) K :=
    fun i j =>
      MvPolynomial.eval
        (rigidLongitudinalUnitPoint (fun _ : Fin 4 => (0 : K)))
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i P.packet))

  have hC :
      C = M.packetAxisHessian := by
    funext i j
    change
      MvPolynomial.eval
          (rigidLongitudinalUnitPoint (fun _ : Fin 4 => (0 : K)))
          (MvPolynomial.pderiv j (MvPolynomial.pderiv i P.packet)) =
        mvHessianComponentAt
          (rigidLongitudinalUnitPoint (fun _ : Fin 4 => (0 : K)))
          P.packet i j
    unfold mvHessianComponentAt
    rw [pderiv_comm_commRing]

  have hblock :
      GeneralFourBlock.ofSymmetricMatrix
          (Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm C) =
        rankTwoPacketAxisFourBlock P.degree P.packet := by
    rw [hC]
    exact M.packetAxisHessian_fourBlock s W P complexity R2

  by_cases hthree : P.degree = 3

  · have hpacket3 :
        IsMinimalLongitudinalSmithPacket
          R2.continuation.subface
          (P.rankOneAnalysisState s W complexity).normalizedSpecialFiber
          3 P.packet := by
      simpa [hthree] using R2.continuation.packetProvenance

    have hiso :
        HasRigidMatrixPacketIsolation 1
          (shiftedRigidMatrixCurveHessian
            3 point M.exposure.family)
          C := by
      simpa [C, point] using
        (shiftedRigidMatrixCurveHessian_cubic_packetIsolation
          M.exposure.family
          point
          hpacket3
          M.exposure.specialFiber_eq
          R2.continuation.quadratic)

    have hle :
        6 * 1 ≤ 3 * M.exposure.defect + 4 := by
      omega

    exact
      rankTwoExactZeroSchurData_of_packetIsolation
        3
        M.exposure.defect
        1
        point
        M.exposure.family
        C
        M.exposure.hessianDefect
        hiso
        hle
        (by simpa [hthree] using hblock)
        (by simpa [hthree] using R2.continuation.escalation)

  · have hfour : 4 ≤ P.degree := by
      omega

    let R : ℕ := 6 * (P.degree - 2)

    have hR :
        2 * (P.degree - 2) < R := by
      dsimp [R]
      omega

    have hiso :
        HasRigidMatrixPacketIsolation (P.degree - 2)
          (shiftedRigidMatrixCurveHessian
            R point M.exposure.family)
          C := by
      simpa [C, point, R] using
        (shiftedRigidMatrixCurveHessian_packetIsolation
          M.exposure.family
          point
          R2.continuation.packetProvenance
          M.exposure.specialFiber_eq
          R2.continuation.quadratic
          hfour
          hR)

    have hRle :
        R ≤ R * M.exposure.defect := by
      have hmul :=
        Nat.mul_le_mul_left R hDelta
      simpa using hmul

    have hle :
        6 * (P.degree - 2) ≤
          R * M.exposure.defect + 4 := by
      dsimp [R] at hRle ⊢
      omega

    exact
      rankTwoExactZeroSchurData_of_packetIsolation
        R
        M.exposure.defect
        (P.degree - 2)
        point
        M.exposure.family
        C
        M.exposure.hessianDefect
        hiso
        hle
        hblock
        R2.continuation.escalation

end

end HC4.Valuation
