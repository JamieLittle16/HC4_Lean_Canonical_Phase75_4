import HC4.Valuation.AdaptiveGeometricRestartState
import HC4.Valuation.AdaptiveRigidMatrixExposure
import HC4.Valuation.AdaptiveSmithWallExposure
import HC4.Newton.RigidPacketEvaluatedHessianChart
import HC4.Newton.RankTwoReesSchurEntry
import Mathlib.Tactic

/-!
# Matrix-level entry for an adaptive rank-two packet

The nondegenerate packet quadratic already singles out source coordinates
`1,2`.  At the distinguished axis point their Hessian principal block is
invertible, while the complementary packet rows have zero coupling.  Thus
rank-two adaptation is a matrix reindexing problem, not a source-coordinate
change.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Packet Hessian chart arranged as the general `2+2` block `(1,2 | 0,3)`.

The persistent-packet support theorem identifies the transverse Hessian
entries with `2A, B, 2C`; all couplings to the complementary coordinates
vanish at the distinguished axis point.  Recording that canonical chart
directly avoids baking an evaluated-source transformation into the
rank-two continuation. -/
noncomputable def rankTwoPacketAxisFourBlock
    (D : ℕ) (Q : MvPolynomial (Fin 4) K) : GeneralFourBlock K :=
  { a := 2 * rankOnePacketCoeffYY (0 : Fin 4) 1 D Q
    b := rankOnePacketCoeffYZ (0 : Fin 4) 1 2 D Q
    d := 2 * rankOnePacketCoeffZZ (0 : Fin 4) 2 D Q
    p := 0
    q := 0
    r := 0
    s := 0
    x := 0
    y := 0
    z := 0 }

/-- Exact active determinant of the transverse packet Hessian. -/
theorem rankTwoPacketAxisFourBlock_activeDet
    [CharZero K]
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K} :
    (rankTwoPacketAxisFourBlock D Q).activeDet =
      - rankOnePacketDiscriminant (0 : Fin 4) 1 2 D Q := by
  unfold rankTwoPacketAxisFourBlock GeneralFourBlock.activeDet
  simp [rankOnePacketDiscriminant]
  ring

/-- Rank-two escalation makes the fixed transverse active block invertible. -/
theorem rankTwoPacketAxisFourBlock_activeDet_ne_zero
    [CharZero K]
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hesc : HasRankTwoPacketEscalation (0 : Fin 4) 1 2 D Q) :
    (rankTwoPacketAxisFourBlock D Q).activeDet ≠ 0 := by
  rw [rankTwoPacketAxisFourBlock_activeDet]
  exact neg_ne_zero.mpr hesc.1

/-- At the axis point the packet has no coupling to the complementary
coordinates `(0,3)`, so its cleared Schur block is identically zero. -/
theorem rankTwoPacketAxisFourBlock_zeroSchur
    [CharZero K]
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K} :
    (rankTwoPacketAxisFourBlock D Q).schurA = 0 ∧
      (rankTwoPacketAxisFourBlock D Q).schurB = 0 ∧
      (rankTwoPacketAxisFourBlock D Q).schurC = 0 := by
  unfold rankTwoPacketAxisFourBlock GeneralFourBlock.schurA
    GeneralFourBlock.schurB GeneralFourBlock.schurC
    GeneralFourBlock.activeDet
  simp

/-- Complete constant-block chart required after matrix packet isolation. -/
theorem rankTwoPacketAxisFourBlock_chart
    [CharZero K]
    {D : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (hesc : HasRankTwoPacketEscalation (0 : Fin 4) 1 2 D Q) :
    (rankTwoPacketAxisFourBlock D Q).activeDet ≠ 0 ∧
      (rankTwoPacketAxisFourBlock D Q).schurA = 0 ∧
      (rankTwoPacketAxisFourBlock D Q).schurB = 0 ∧
      (rankTwoPacketAxisFourBlock D Q).schurC = 0 := by
  exact ⟨rankTwoPacketAxisFourBlock_activeDet_ne_zero hesc,
    rankTwoPacketAxisFourBlock_zeroSchur⟩

/-- The canonical matrix ordering `(1,2 | 0,3)`. -/
def rankTwoAxisPerm : Equiv.Perm (Fin 4) :=
  (Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)

@[simp] theorem rankTwoAxisPerm_zero : rankTwoAxisPerm 0 = 1 := by decide
@[simp] theorem rankTwoAxisPerm_one : rankTwoAxisPerm 1 = 2 := by decide
@[simp] theorem rankTwoAxisPerm_two : rankTwoAxisPerm 2 = 0 := by decide
@[simp] theorem rankTwoAxisPerm_three : rankTwoAxisPerm 3 = 3 := by decide

private theorem pderiv_two_zero_rankTwoAxis (i : Fin 4) :
    MvPolynomial.pderiv i (2 : MvPolynomial (Fin 4) K) = 0 := by
  have htwo : (2 : MvPolynomial (Fin 4) K) = 1 + 1 := by norm_num
  rw [htwo]
  simp only [map_add, MvPolynomial.pderiv_one, add_zero]

set_option maxHeartbeats 1000000 in
/-- All ten scalar entries of the packet Hessian at the longitudinal axis.
Keeping this as small scalar calculations avoids expanding a complete
four-block inside one simplifier invocation. -/
theorem rankTwoPacketAxisHessian_entries
    {D : ℕ} {Q : MvPolynomial (Fin 4) K}
    (hpacket : HasRankOnePersistentPacketSupport (0 : Fin 4) 1 2 D Q) :
    let pt := rigidLongitudinalUnitPoint (fun _ => (0 : K))
    mvHessianComponentAt pt Q 1 1 =
        2 * rankOnePacketCoeffYY (0 : Fin 4) 1 D Q ∧
    mvHessianComponentAt pt Q 1 2 =
        rankOnePacketCoeffYZ (0 : Fin 4) 1 2 D Q ∧
    mvHessianComponentAt pt Q 2 2 =
        2 * rankOnePacketCoeffZZ (0 : Fin 4) 2 D Q ∧
    mvHessianComponentAt pt Q 1 0 = 0 ∧
    mvHessianComponentAt pt Q 1 3 = 0 ∧
    mvHessianComponentAt pt Q 2 0 = 0 ∧
    mvHessianComponentAt pt Q 2 3 = 0 ∧
    mvHessianComponentAt pt Q 0 0 = 0 ∧
    mvHessianComponentAt pt Q 0 3 = 0 ∧
    mvHessianComponentAt pt Q 3 3 = 0 := by
  have hmodel := rankOnePersistentPacket_eq_algebraicModel
    (by decide : (0 : Fin 4) ≠ 1) (by decide : (0 : Fin 4) ≠ 2)
    (by decide : (1 : Fin 4) ≠ 2) hpacket
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 1 1) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis]
        ring_nf)
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 1 2) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 2 2) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis]
        ring_nf)
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 1 0) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 1 3) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 2 0) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 2 3) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 0 0) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 0 3) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])
  · exact (congrArg (fun G => mvHessianComponentAt
      (rigidLongitudinalUnitPoint (fun _ => (0 : K))) G 3 3) hmodel).trans
      (by
        unfold mvHessianComponentAt rankOnePacketAlgebraicModel
        simp [-standardTwoZero_pderiv_two_eq_A,
          -standardTwoZero_pderiv_three_eq_C,
          rigidLongitudinalUnitPoint, standardTwoZeroA,
          standardTwoZeroC, pderiv_two_zero_rankTwoAxis])

/-- The reindexed packet Hessian is exactly the canonical transverse
rank-two four-block. -/
theorem rankTwoPacket_reindexedAxisHessian_eq_fourBlock
    {D : ℕ} {Q : MvPolynomial (Fin 4) K}
    (hpacket : HasRankOnePersistentPacketSupport (0 : Fin 4) 1 2 D Q) :
    GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm
          (fun i j => mvHessianComponentAt
            (rigidLongitudinalUnitPoint (fun _ => (0 : K))) Q i j)) =
      rankTwoPacketAxisFourBlock D Q := by
  rcases rankTwoPacketAxisHessian_entries hpacket with
    ⟨h11, h12, h22, h10, h13, h20, h23, h00, h03, h33⟩
  apply GeneralFourBlock.ext <;>
    simp [GeneralFourBlock.ofSymmetricMatrix, rankTwoPacketAxisFourBlock,
      h11, h12, h22, h10, h13, h20, h23, h00, h03, h33]

/-! ## Normalization-preserving rank-two reindexing -/

theorem rankTwoAxisPerm_preserves_normalizationExponent
    (n : ℕ) (i : Fin 4) :
    rigidMatrixNormalizationExponent n (rankTwoAxisPerm i) =
      rigidMatrixNormalizationExponent n i := by
  fin_cases i <;> simp [rigidMatrixNormalizationExponent]

/-- Packet isolation is invariant under simultaneous row/column reindexing
whenever the permutation preserves the normalization exponents. -/
theorem HasRigidMatrixPacketIsolation.reindex
    {n : ℕ}
    {H : Matrix (Fin 4) (Fin 4) (Polynomial K)}
    {C : Matrix (Fin 4) (Fin 4) K}
    (hiso : HasRigidMatrixPacketIsolation n H C)
    (rho : Equiv.Perm (Fin 4))
    (hpres : ∀ i, rigidMatrixNormalizationExponent n (rho i) =
      rigidMatrixNormalizationExponent n i) :
    HasRigidMatrixPacketIsolation n
      (Matrix.reindex rho.symm rho.symm H)
      (Matrix.reindex rho.symm rho.symm C) := by
  intro i j
  rcases hiso (rho i) (rho j) with ⟨tail, htail⟩
  refine ⟨tail, ?_⟩
  simpa [hpres i, hpres j] using htail

/-- The canonical rank-two permutation preserves packet isolation. -/
theorem HasRigidMatrixPacketIsolation.reindexRankTwoAxis
    {n : ℕ}
    {H : Matrix (Fin 4) (Fin 4) (Polynomial K)}
    {C : Matrix (Fin 4) (Fin 4) K}
    (hiso : HasRigidMatrixPacketIsolation n H C) :
    HasRigidMatrixPacketIsolation n
      (Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm H)
      (Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm C) :=
  hiso.reindex rankTwoAxisPerm
    (rankTwoAxisPerm_preserves_normalizationExponent n)

theorem det_reindexRankTwoAxis
    (H : Matrix (Fin 4) (Fin 4) (Polynomial K)) :
    (Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm H).det = H.det :=
  Matrix.det_reindex_self rankTwoAxisPerm.symm H

/-- Generic handoff from a packet-isolated Hessian to the rank-two
zero-Schur clock after the canonical `(1,2 | 0,3)` reindexing. -/
noncomputable def rankTwoExactZeroSchurData_of_packetIsolation
    [CharZero K]
    (R Delta n : ℕ)
    (point : Fin 4 → K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (C : Matrix (Fin 4) (Fin 4) K)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (hiso : HasRigidMatrixPacketIsolation n
      (shiftedRigidMatrixCurveHessian R point P) C)
    (hle : 6 * n ≤ R * Delta + 4)
    {D : ℕ} {Q : MvPolynomial (Fin 4) K}
    (hblock : GeneralFourBlock.ofSymmetricMatrix
        (Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm C) =
      rankTwoPacketAxisFourBlock D Q)
    (hesc : HasRankTwoPacketEscalation (0 : Fin 4) 1 2 D Q) :
    ExactZeroSchurFourBlockData K := by
  let H := shiftedRigidMatrixCurveHessian R point P
  let H' := Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm H
  let C' := Matrix.reindex rankTwoAxisPerm.symm rankTwoAxisPerm.symm C
  have hiso' : HasRigidMatrixPacketIsolation n H' C' :=
    hiso.reindexRankTwoAxis
  apply exactZeroSchurFourBlockData_of_packetIsolation
    n (R * Delta + 4 - 6 * n) H' C' hiso'
  · intro i j
    change H (rankTwoAxisPerm i) (rankTwoAxisPerm j) =
      H (rankTwoAxisPerm j) (rankTwoAxisPerm i)
    exact shiftedRigidMatrixCurveHessian_symmetric R point P _ _
  · apply det_integralRigidMatrixNormalization_eq_X_pow_sub
      n (R * Delta + 4) H' hiso'.integral
    · change H'.det = Polynomial.X ^ (R * Delta + 4)
      rw [show H'.det = H.det from det_reindexRankTwoAxis H]
      exact det_shiftedRigidMatrixCurveHessian R Delta point P hdef
    · exact hle
  · rw [hblock]
    exact rankTwoPacketAxisFourBlock_chart hesc

/-! ## Honest construction from an adaptive integral wall -/

/-- The coefficientwise adaptive Smith exposure constructs the actual
family-level object required by rank-two packet isolation.  In particular,
the family and the packet are connected by the exact balanced-subface
special-fibre identity rather than merely stored side by side. -/
noncomputable def AdaptiveRankTwoFamilyContinuation.toMatrixExposure
    {s : AdaptiveGeometricRestartState (K := K)}
    {D complexity : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (c : AdaptiveRankTwoFamilyContinuation s D complexity Q)
    (m : ℕ)
    (hm : (m : ℤ) =
      c.integralWall.realization.combinedSourceLevel c.integralWall.level)
    (ram : AdaptiveSmithExposureRamificationData
      c.integralWall.realization.combinedSourceWeight m s.defect) :
    AdaptiveRankTwoMatrixExposure s D complexity Q c := by
  let wall := c.integralWall
  let P := zeroJetNormalizedFamily s.family
  let hint : HasIntegralAdaptiveSmithExposure ram.R
      wall.realization.combinedSourceWeight m P :=
    HC4.Valuation.IntegralAdaptiveSurvivingSmithWall.hasIntegralAdaptiveSmithExposure
      P wall m hm ram
  let Pexp := adaptiveSmithExposureFamily ram.R
    wall.realization.combinedSourceWeight m P hint
  refine
    { family := Pexp
      defect := ram.R * s.defect +
        2 * ∑ i : Fin 4, wall.realization.combinedSourceWeight i - 4 * m
      hessianDefect := ?_
      specialFiber_eq := ?_ }
  · exact adaptiveSmithExposureFamily_hasHessianDefect
      ram.R wall.realization.combinedSourceWeight m s.defect ram rfl
      P hint s.normalized_hessianDefect
  · have hspecial :=
      HC4.Valuation.IntegralAdaptiveSurvivingSmithWall.specialFiber_adaptiveSmithExposureFamily
        P wall m hm ram hint
    simpa [Pexp, P, AdaptiveGeometricRestartState.normalizedSpecialFiber,
      c.subface_eq_balanced] using hspecial

end

end HC4.Valuation
