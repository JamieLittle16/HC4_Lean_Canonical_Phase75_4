import HC4.Valuation.AdaptiveAlignedSmithExposureGeometry
import HC4.Valuation.AdaptiveAlignedSmithPacketRepair
import HC4.Valuation.AdaptiveRigidMatrixExposure
import HC4.Valuation.AdaptiveRankTwoMatrixExposure
import HC4.Newton.RigidPacketEvaluatedHessianChart
import Mathlib.Tactic

/-!
# Adaptive surviving rigid packet to exact zero-Schur closing data

The surviving aligned-Smith packet is not the whole special fibre of the
incoming family; it is the first longitudinal homogeneous piece of the exact
balanced Smith subface.  `AdaptiveSurvivingWallExposureData` constructs the
honest coefficientwise exposed family whose special fibre is that complete
balanced subface, while `AdaptiveRigidMatrixExposure` isolates the retained
minimal packet on the shifted Hessian curve.

This file joins those two already-green interfaces.  It handles both rigid
pivot charts.  The right-axis chart uses the existing normalization-preserving
simultaneous matrix reindexing, so no new Schur algebra is introduced.

Consequently a surviving rigid packet of degree at least three is no longer a
raw global dispatcher branch: either the incoming exposed clock is already
zero, or the exact zero-Schur clock gives strict rank-two repair progress, or
one retains source-honest zero-Schur closing data.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-! ## The two scalar packet charts -/

noncomputable def adaptiveRigidLeftPoint : Fin 4 → K :=
  rankOnePacketTransversePoint (0 : Fin 4) 1 2 (1 : K) 0

noncomputable def adaptiveRigidRightPoint : Fin 4 → K :=
  rankOnePacketTransversePoint (0 : Fin 4) 1 2 (0 : K) 1

def adaptiveRigidRightPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) 2

@[simp] theorem adaptiveRigidRightPerm_zero :
    adaptiveRigidRightPerm (0 : Fin 4) = 0 := by decide
@[simp] theorem adaptiveRigidRightPerm_one :
    adaptiveRigidRightPerm (1 : Fin 4) = 2 := by decide
@[simp] theorem adaptiveRigidRightPerm_two :
    adaptiveRigidRightPerm (2 : Fin 4) = 1 := by decide
@[simp] theorem adaptiveRigidRightPerm_three :
    adaptiveRigidRightPerm (3 : Fin 4) = 3 := by decide

@[simp] theorem adaptiveRigidRightPerm_symm :
    adaptiveRigidRightPerm.symm = adaptiveRigidRightPerm := by
  ext i
  fin_cases i <;> decide

/-- Swapping coordinates `1` and `2` preserves the rigid matrix
normalization exponents. -/
theorem adaptiveRigidRightPerm_preserves_normalizationExponent
    (n : ℕ) (i : Fin 4) :
    rigidMatrixNormalizationExponent n (adaptiveRigidRightPerm i) =
      rigidMatrixNormalizationExponent n i := by
  fin_cases i <;> simp [rigidMatrixNormalizationExponent]

/-- The longitudinal-unit evaluation used by matrix isolation is exactly the
left rigid packet point. -/
theorem rigidLongitudinalUnitPoint_adaptiveRigidLeftPoint :
    rigidLongitudinalUnitPoint (adaptiveRigidLeftPoint (K := K)) =
      adaptiveRigidLeftPoint := by
  funext i
  fin_cases i <;>
    simp [rigidLongitudinalUnitPoint, adaptiveRigidLeftPoint,
      rankOnePacketTransversePoint]

/-- Right-axis analogue. -/
theorem rigidLongitudinalUnitPoint_adaptiveRigidRightPoint :
    rigidLongitudinalUnitPoint (adaptiveRigidRightPoint (K := K)) =
      adaptiveRigidRightPoint := by
  funext i
  fin_cases i <;>
    simp [rigidLongitudinalUnitPoint, adaptiveRigidRightPoint,
      rankOnePacketTransversePoint]

/-- The packet matrix used by adaptive rigid isolation is exactly the old
left rigid scalar Hessian block. -/
theorem adaptiveRigidLeftPacketMatrix_fourBlock
    (D : ℕ) (Q : MvPolynomial (Fin 4) K) :
    GeneralFourBlock.ofSymmetricMatrix
        (fun i j =>
          MvPolynomial.eval
            (rigidLongitudinalUnitPoint (adaptiveRigidLeftPoint (K := K)))
            (HC4.Polynomial.hessian Q i j)) =
      rigidPacketLeftHessianBlock D Q := by
  rw [rigidLongitudinalUnitPoint_adaptiveRigidLeftPoint]
  apply GeneralFourBlock.ext <;>
    simp [-standardTwoZero_pderiv_two_eq_A,
      -standardTwoZero_pderiv_three_eq_C,
      GeneralFourBlock.ofSymmetricMatrix,
      rigidPacketLeftHessianBlock, mvHessianComponentAt,
      adaptiveRigidLeftPoint, HC4.Polynomial.hessian_apply,
      standardTwoZeroA, standardTwoZeroC, pderiv_comm_commRing]

/-- After the `(1 2)` reindexing, the adaptive packet matrix is exactly the
right-axis scalar Hessian block. -/
theorem adaptiveRigidRightPacketMatrix_fourBlock
    (D : ℕ) (Q : MvPolynomial (Fin 4) K) :
    GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm
          (fun i j =>
            MvPolynomial.eval
              (rigidLongitudinalUnitPoint (adaptiveRigidRightPoint (K := K)))
              (HC4.Polynomial.hessian Q i j))) =
      rigidPacketRightHessianBlock D Q := by
  rw [rigidLongitudinalUnitPoint_adaptiveRigidRightPoint]
  apply GeneralFourBlock.ext <;>
    simp [-standardTwoZero_pderiv_two_eq_A,
      -standardTwoZero_pderiv_three_eq_C,
      GeneralFourBlock.ofSymmetricMatrix,
      rigidPacketRightHessianBlock, mvHessianComponentAt,
      adaptiveRigidRightPoint,
      HC4.Polynomial.hessian_apply, standardTwoZeroA, standardTwoZeroC,
      pderiv_comm_commRing]

/-! ## Right-axis reindexed exact zero-Schur constructor -/

/-- Generic right-chart handoff from one packet-isolated shifted Hessian.
The simultaneous `(1 2)` permutation preserves every normalization exponent,
so the determinant clock is unchanged. -/
noncomputable def adaptiveRigidMatrixRightZeroSchurData
    (R Delta n : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (C : Matrix (Fin 4) (Fin 4) K)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hiso : HasRigidMatrixPacketIsolation n
      (shiftedRigidMatrixCurveHessian R point P) C)
    (hle : 6 * n ≤ R * Delta + 4)
    (hchart :
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).activeDet ≠ 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).schurA = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).schurB = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).schurC = 0) :
    ExactZeroSchurFourBlockData K := by
  let H := shiftedRigidMatrixCurveHessian R point P
  have hisoR :
      HasRigidMatrixPacketIsolation n
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm H)
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C) :=
    hiso.reindex adaptiveRigidRightPerm
      (adaptiveRigidRightPerm_preserves_normalizationExponent n)
  have hsymmR :
      ∀ i j,
        Matrix.reindex adaptiveRigidRightPerm.symm
            adaptiveRigidRightPerm.symm H i j =
          Matrix.reindex adaptiveRigidRightPerm.symm
            adaptiveRigidRightPerm.symm H j i := by
    intro i j
    simpa [H] using
      (shiftedRigidMatrixCurveHessian_symmetric R point P
        (adaptiveRigidRightPerm i) (adaptiveRigidRightPerm j))
  have hdetH :
      (Matrix.reindex adaptiveRigidRightPerm.symm
        adaptiveRigidRightPerm.symm H).det =
          Polynomial.X ^ (R * Delta + 4) := by
    calc
      (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm H).det = H.det := by
        exact Matrix.det_reindex_self adaptiveRigidRightPerm.symm H
      _ = Polynomial.X ^ (R * Delta + 4) := by
        simpa [H] using
          (det_shiftedRigidMatrixCurveHessian R Delta point P hdef)
  have hdetNorm :
      (integralRigidMatrixNormalization n
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm H) hisoR.integral).det =
          Polynomial.X ^ (R * Delta + 4 - 6 * n) :=
    det_integralRigidMatrixNormalization_eq_X_pow_sub
      n (R * Delta + 4)
      (Matrix.reindex adaptiveRigidRightPerm.symm
        adaptiveRigidRightPerm.symm H)
      hisoR.integral hdetH hle
  exact exactZeroSchurFourBlockData_of_packetIsolation
    n (R * Delta + 4 - 6 * n)
    (Matrix.reindex adaptiveRigidRightPerm.symm
      adaptiveRigidRightPerm.symm H)
    (Matrix.reindex adaptiveRigidRightPerm.symm
      adaptiveRigidRightPerm.symm C)
    hisoR hsymmR hdetNorm hchart

/-! ## One exposed surviving rigid packet -/

/-- The rigid packet always chooses one of the two concrete pivot charts. -/
theorem AdaptiveAlignedSmithRigidPacketEndpoint.pivot
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P) :
    (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 P.degree P.packet).LeftPivot ∨
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 P.degree P.packet).RightAxisPivot := by
  rcases R.rigid.2 with hleft | hright
  · exact Or.inl hleft.1
  · exact Or.inr hright.1

/-- Left-pivot rigid packet on an honest surviving-wall exposure gives exact
zero-Schur four-block data. -/
noncomputable def AdaptiveAlignedSmithRigidPacketEndpoint.leftZeroSchurData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (hD : 3 ≤ P.degree)
    (hleft :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 P.degree P.packet).LeftPivot) :
    ExactZeroSchurFourBlockData K := by
  let point := adaptiveRigidLeftPoint (K := K)
  have hspecial :
      polynomialFamilySpecialFiber d.family =
        smithSubfacePolynomial (1 : Fin 4) 2 3
          (W.balancedSubface s)
          (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber := by
    simpa [AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface] using
      d.specialFiber_eq_balancedSubface
  have hchart0 :=
    rigidPacket_left_zeroSchurChart
      P.persistent R.rigid hleft hD
  have hchart :
      let C : Matrix (Fin 4) (Fin 4) K := fun i j =>
        MvPolynomial.eval (rigidLongitudinalUnitPoint point)
          (HC4.Polynomial.hessian P.packet i j)
      (GeneralFourBlock.ofSymmetricMatrix C).activeDet ≠ 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurA = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurB = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix C).schurC = 0 := by
    dsimp only
    rw [adaptiveRigidLeftPacketMatrix_fourBlock P.degree P.packet]
    exact hchart0
  by_cases hthree : P.degree = 3
  · have hpacket3 :
        IsMinimalLongitudinalSmithPacket
          (W.balancedSubface s)
          (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber
          3 P.packet := by
      simpa [hthree] using P.provenance
    exact cubicAdaptiveRigidMatrixZeroSchurData
      d.defect d.family point d.hessianDefect hpacket3 hspecial
      P.quadratic hchart
  · have hfour : 4 ≤ P.degree := by omega
    exact higherAdaptiveRigidMatrixZeroSchurData
      P.degree d.defect d.family point hfour d.hessianDefect
      P.provenance hspecial P.quadratic hchart

/-- Right-axis analogue, using normalization-preserving simultaneous
reindexing before forming the four-block. -/
noncomputable def AdaptiveAlignedSmithRigidPacketEndpoint.rightZeroSchurData
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (hD : 3 ≤ P.degree)
    (hright :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 P.degree P.packet).RightAxisPivot) :
    ExactZeroSchurFourBlockData K := by
  let point := adaptiveRigidRightPoint (K := K)
  let C : Matrix (Fin 4) (Fin 4) K := fun i j =>
    MvPolynomial.eval (rigidLongitudinalUnitPoint point)
      (HC4.Polynomial.hessian P.packet i j)
  have hspecial :
      polynomialFamilySpecialFiber d.family =
        smithSubfacePolynomial (1 : Fin 4) 2 3
          (W.balancedSubface s)
          (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber := by
    simpa [AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface] using
      d.specialFiber_eq_balancedSubface
  have hchart0 := rigidPacket_right_zeroSchurChart
    P.persistent hright hD
  have hchart :
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).activeDet ≠ 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).schurA = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).schurB = 0 ∧
      (GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C)).schurC = 0 := by
    rw [show GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex adaptiveRigidRightPerm.symm
          adaptiveRigidRightPerm.symm C) =
        rigidPacketRightHessianBlock P.degree P.packet by
      simpa [C, point] using
        (adaptiveRigidRightPacketMatrix_fourBlock
          (K := K) P.degree P.packet)]
    exact hchart0
  by_cases hthree : P.degree = 3
  · have hpacket3 :
        IsMinimalLongitudinalSmithPacket
          (W.balancedSubface s)
          (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber
          3 P.packet := by
      simpa [hthree] using P.provenance
    have hiso := shiftedRigidMatrixCurveHessian_cubic_packetIsolation
      d.family point hpacket3 hspecial P.quadratic
    have hle : 6 * 1 ≤ 3 * d.defect + 4 := by
      have hpos := quadraticSmithSpecialFiber_hessianDefect_pos
        d.hessianDefect hspecial P.quadratic
      omega
    exact adaptiveRigidMatrixRightZeroSchurData
      3 d.defect 1 point d.family C d.hessianDefect hiso hle hchart
  · have hfour : 4 ≤ P.degree := by omega
    let ram : ℕ := 6 * P.degree - 16
    have hram : 2 * (P.degree - 2) < ram := by
      dsimp [ram]
      omega
    have hiso := shiftedRigidMatrixCurveHessian_packetIsolation
      d.family point P.provenance hspecial P.quadratic hfour hram
    have hDelta := quadraticSmithSpecialFiber_hessianDefect_pos
      d.hessianDefect hspecial P.quadratic
    have hramle : ram ≤ ram * d.defect := by
      exact Nat.le_mul_of_pos_right ram hDelta
    have hle : 6 * (P.degree - 2) ≤ ram * d.defect + 4 := by
      dsimp [ram] at hramle ⊢
      omega
    exact adaptiveRigidMatrixRightZeroSchurData
      ram d.defect (P.degree - 2) point d.family C
      d.hessianDefect hiso hle hchart

/-- Source-honest closing output for one surviving rigid packet. -/
structure AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P) where
  exposure : AdaptiveSurvivingWallExposureData
    (W.original.aligned.toAdaptiveState s) W.wall
  zeroSchur : ExactZeroSchurFourBlockData K
  closing :
    (zeroSchur.toClock.residualDefect = 0 ∧
      zeroSchur.toClock.tailSeries.active.coeff 0 *
          zeroSchur.toClock.tailSeries.kernel.coeff 0 -
        zeroSchur.toClock.tailSeries.offDiag.coeff 0 *
          zeroSchur.toClock.tailSeries.offDiag.coeff 0 ≠ 0) ∨
    (∃ S : ExactRankOneSchurClockAt K,
      0 < zeroSchur.toClock.residualDefect ∧
      S.defect = zeroSchur.toClock.residualDefect ∧
      S.firstOrder = S.defect ∧
      (S.series.offDiag.coeff S.defect ≠ 0 ∨
       S.series.kernel.coeff S.defect ≠ 0))

/-- **Surviving rigid packet is consumed by the adaptive exposure clock.**

The only outputs are literal zero defect on the source aligned state, strict
rank-two repair progress, or source-honest zero-Schur closing data. -/
theorem AdaptiveAlignedSmithRigidPacketEndpoint.zeroDefect_or_rankTwoProgress_or_closing
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (hD : 3 ≤ P.degree)
    (complexity : ℕ) :
    (W.original.aligned.toAdaptiveState s).defect = 0 ∨
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      Nonempty
        (AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
          (K := K) s W P R) := by
  rcases W.zeroDefect_or_exposure s with hzero | hexposure
  · exact Or.inl hzero
  · let d : AdaptiveSurvivingWallExposureData
        (W.original.aligned.toAdaptiveState s) W.wall :=
      Classical.choice hexposure
    rcases R.pivot s W P with hleft | hright
    · let Z : ExactZeroSchurFourBlockData K :=
        R.leftZeroSchurData s W P d hD hleft
      rcases Z.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inr (Or.inl hprogress)
      · exact Or.inr (Or.inr
          ⟨{
            exposure := d
            zeroSchur := Z
            closing := hclosing
          }⟩)
    · let Z : ExactZeroSchurFourBlockData K :=
        R.rightZeroSchurData s W P d hD hright
      rcases Z.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inr (Or.inl hprogress)
      · exact Or.inr (Or.inr
          ⟨{
            exposure := d
            zeroSchur := Z
            closing := hclosing
          }⟩)

end

end HC4.Valuation
