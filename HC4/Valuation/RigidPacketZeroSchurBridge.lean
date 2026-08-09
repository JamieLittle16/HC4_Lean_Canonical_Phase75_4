import HC4.Valuation.CanonicalSmithDefectExposure
import HC4.Valuation.SmithFrontierFourBlockExtraction
import HC4.Valuation.QuadraticFamilyCollision
import HC4.Newton.RigidPacketEvaluatedHessianChart
import HC4.Newton.ZeroSchurFirstEntryClock
import Mathlib.Tactic

/-!
# Defect-exposure Hessian to the two-stage zero-Schur clock

Phase 75.10 constructs the defect-preserving Smith exposure `P♯` with

    det Hess(P♯) = X^(20*Delta)

and special fibre equal to the retained canonical Smith packet.

The rigid packet calculation in `RigidPacketEvaluatedHessianChart` should
not be imposed as a polynomial identity over the whole spatial affine space.
Instead we evaluate the Hessian at one fixed scalar spatial point.  Since the
Hessian determinant clock is the spatial constant polynomial `X^N`, this
spatial evaluation preserves the exact clock.

For `D ≥ 3`, a rigid packet has one of two scalar charts:

* left pivot: evaluate at `(1,1,0,0)` and use active coordinates `(0,1)`;
* right-axis pivot: evaluate at `(1,0,1,0)` and use active coordinates `(0,2)`.

At the special fibre the active minor is nonzero and the denominator-cleared
Schur block is zero.  Hence the resulting polynomial-valued four-block is
exactly an `ExactZeroSchurFourBlockData`, and the entire green two-stage
Schur clock applies.

The current retained frontier records only `2 ≤ D`.  Accordingly the final
theorem in this file closes every rigid branch with `D ≥ 3` and isolates the
single honest boundary `D = 2` rather than assuming away that case.
-/

namespace HC4.Valuation

open HC4.Newton
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

/-! ## Spatial evaluation of a polynomial-parameter Hessian -/

/-- Evaluate the spatial variables of a polynomial-parameter polynomial at
a constant scalar point, leaving the parameter polynomial untouched. -/
noncomputable def constantSpatialEval
    (point : Fin 4 → K) :
    MvPolynomial (Fin 4) (Polynomial K) →+* Polynomial K :=
  MvPolynomial.eval (polynomialConstantSection point)

/-- The family Hessian after scalar spatial evaluation. -/
noncomputable def evaluatedFamilyHessian
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  (constantSpatialEval point).mapMatrix (HC4.Polynomial.hessian P)

/-- Spatial evaluation preserves Hessian symmetry. -/
theorem evaluatedFamilyHessian_symmetric
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    (i j : Fin 4) :
    evaluatedFamilyHessian P point i j =
      evaluatedFamilyHessian P point j i := by
  change
    constantSpatialEval point
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i P)) =
      constantSpatialEval point
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j P))
  congr 1
  exact (pderiv_comm_commRing i j P).symm

/-- The constant parameter coefficient of an evaluated family Hessian entry
is the corresponding actual Hessian entry of the special fibre. -/
theorem evaluatedFamilyHessian_coeff_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    (i j : Fin 4) :
    (evaluatedFamilyHessian P point i j).coeff 0 =
      mvHessianComponentAt point (polynomialFamilySpecialFiber P) i j := by
  have h :=
    polynomialFamilySpecialFiber_gradientComponent
      (P := MvPolynomial.pderiv i P)
      (a := polynomialConstantSection point)
      j
  have hji :
      (evaluatedFamilyHessian P point i j).coeff 0 =
        mvHessianComponentAt point (polynomialFamilySpecialFiber P) j i := by
    simpa [evaluatedFamilyHessian, constantSpatialEval,
      HC4.Polynomial.hessian_apply,
      mvGradientComponentAt, mvHessianComponentAt,
      polynomialFamilySpecialFiber, MvPolynomial.pderiv_map] using h.symm
  calc
    (evaluatedFamilyHessian P point i j).coeff 0 =
        mvHessianComponentAt point (polynomialFamilySpecialFiber P) j i := hji
    _ = mvHessianComponentAt point (polynomialFamilySpecialFiber P) i j := by
      unfold mvHessianComponentAt
      rw [pderiv_comm_commRing]

/-- Spatial evaluation preserves an exact pure Hessian determinant clock. -/
theorem evaluatedFamilyHessian_det_eq_X_pow
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    (evaluatedFamilyHessian P point).det = Polynomial.X ^ Delta := by
  unfold evaluatedFamilyHessian
  calc
    ((constantSpatialEval point).mapMatrix
        (HC4.Polynomial.hessian P)).det =
      constantSpatialEval point
        (HC4.Polynomial.hessianDeterminant P) := by
          exact
            ((constantSpatialEval point).map_det
              (HC4.Polynomial.hessian P)).symm
    _ = constantSpatialEval point
        (MvPolynomial.C (Polynomial.X ^ Delta)) := by
          rw [hdef]
    _ = Polynomial.X ^ Delta := by
          simp [constantSpatialEval, polynomialConstantSection]

/-! ## Repacking a permuted evaluated Hessian -/

/-- Reorder rows and columns simultaneously and package the result as a
symmetric general four-block. -/
noncomputable def evaluatedFamilyHessianFourBlock
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K) :
    GeneralFourBlock (Polynomial K) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((evaluatedFamilyHessian P point).submatrix rho rho)

/-- The displayed matrix of the evaluated four-block is exactly the
simultaneously permuted evaluated Hessian. -/
theorem evaluatedFamilyHessianFourBlock_matrix
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K) :
    (evaluatedFamilyHessianFourBlock rho P point).matrix =
      (evaluatedFamilyHessian P point).submatrix rho rho := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact evaluatedFamilyHessian_symmetric P point (rho i) (rho j)

/-- Repacking and simultaneous coordinate permutation preserve the exact
determinant clock. -/
theorem evaluatedFamilyHessianFourBlock_determinantCore_eq_X_pow
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K)
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    (evaluatedFamilyHessianFourBlock rho P point).determinantCore =
      Polynomial.X ^ Delta := by
  calc
    (evaluatedFamilyHessianFourBlock rho P point).determinantCore =
        (evaluatedFamilyHessianFourBlock rho P point).matrix.det :=
      (GeneralFourBlock.matrix_det
        (evaluatedFamilyHessianFourBlock rho P point)).symm
    _ = ((evaluatedFamilyHessian P point).submatrix rho rho).det := by
      rw [evaluatedFamilyHessianFourBlock_matrix]
    _ = (evaluatedFamilyHessian P point).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = Polynomial.X ^ Delta :=
      evaluatedFamilyHessian_det_eq_X_pow P point hdef

/-- Fixed coordinate permutation used by the right-axis rigid chart:
positions `1` and `2` are interchanged so `(0,2)` becomes the active pair. -/
def rigidRightChartPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) 2

/-- The right-chart permutation fixes coordinate `0`.  Keeping this as an
explicit simp lemma prevents `simp` from expanding `Equiv.swap` inside the
large Schur expressions below. -/
@[simp] theorem rigidRightChartPerm_zero :
    rigidRightChartPerm (0 : Fin 4) = 0 := by
  decide

/-- The right-chart permutation sends position `1` to source coordinate `2`. -/
@[simp] theorem rigidRightChartPerm_one :
    rigidRightChartPerm (1 : Fin 4) = 2 := by
  decide

/-- The right-chart permutation sends position `2` to source coordinate `1`. -/
@[simp] theorem rigidRightChartPerm_two :
    rigidRightChartPerm (2 : Fin 4) = 1 := by
  decide

/-- The right-chart permutation fixes coordinate `3`. -/
@[simp] theorem rigidRightChartPerm_three :
    rigidRightChartPerm (3 : Fin 4) = 3 := by
  decide

/-- Left rigid chart point `(x,y,z,w)=(1,1,0,0)`. -/
noncomputable def rigidLeftChartPoint : Fin 4 → K :=
  rankOnePacketTransversePoint (0 : Fin 4) 1 2 (1 : K) 0

/-- Right-axis rigid chart point `(x,y,z,w)=(1,0,1,0)`. -/
noncomputable def rigidRightChartPoint : Fin 4 → K :=
  rankOnePacketTransversePoint (0 : Fin 4) 1 2 (0 : K) 1

/-- The parameter-family block used in the left rigid chart. -/
noncomputable def rigidExposureLeftFourBlock
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    GeneralFourBlock (Polynomial K) :=
  evaluatedFamilyHessianFourBlock (Equiv.refl (Fin 4)) P
    rigidLeftChartPoint

/-- The parameter-family block used in the right rigid chart. -/
noncomputable def rigidExposureRightFourBlock
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    GeneralFourBlock (Polynomial K) :=
  evaluatedFamilyHessianFourBlock rigidRightChartPerm P
    rigidRightChartPoint


/-- Apply the parameter constant-coefficient homomorphism entrywise to a
polynomial-valued four-block.  This keeps the large Schur expressions out of
coordinate-permutation proofs: we first specialise the ten entries, then use
ordinary scalar four-block algebra. -/
noncomputable def constantCoeffFourBlock
    (H : GeneralFourBlock (Polynomial K)) : GeneralFourBlock K where
  a := H.a.coeff 0
  b := H.b.coeff 0
  d := H.d.coeff 0
  p := H.p.coeff 0
  q := H.q.coeff 0
  r := H.r.coeff 0
  s := H.s.coeff 0
  x := H.x.coeff 0
  y := H.y.coeff 0
  z := H.z.coeff 0

/-- Constant coefficient commutes with the active `2 x 2` determinant. -/
theorem constantCoeffFourBlock_activeDet
    (H : GeneralFourBlock (Polynomial K)) :
    H.activeDet.coeff 0 = (constantCoeffFourBlock H).activeDet := by
  simp [constantCoeffFourBlock, GeneralFourBlock.activeDet,
    Polynomial.coeff_zero_eq_eval_zero]

/-- Constant coefficient commutes with the first cleared Schur entry. -/
theorem constantCoeffFourBlock_schurA
    (H : GeneralFourBlock (Polynomial K)) :
    H.schurA.coeff 0 = (constantCoeffFourBlock H).schurA := by
  simp [constantCoeffFourBlock, GeneralFourBlock.schurA,
    GeneralFourBlock.activeDet, Polynomial.coeff_zero_eq_eval_zero]

/-- Constant coefficient commutes with the cleared off-diagonal Schur entry. -/
theorem constantCoeffFourBlock_schurB
    (H : GeneralFourBlock (Polynomial K)) :
    H.schurB.coeff 0 = (constantCoeffFourBlock H).schurB := by
  simp [constantCoeffFourBlock, GeneralFourBlock.schurB,
    GeneralFourBlock.activeDet, Polynomial.coeff_zero_eq_eval_zero]

/-- Constant coefficient commutes with the kernel cleared Schur entry. -/
theorem constantCoeffFourBlock_schurC
    (H : GeneralFourBlock (Polynomial K)) :
    H.schurC.coeff 0 = (constantCoeffFourBlock H).schurC := by
  simp [constantCoeffFourBlock, GeneralFourBlock.schurC,
    GeneralFourBlock.activeDet, Polynomial.coeff_zero_eq_eval_zero]

/-- Specialising the ten entries of an evaluated family Hessian four-block at
parameter `0` gives the four-block of the evaluated special-fibre Hessian.
This is deliberately entrywise, so no Schur polynomial is expanded here. -/
theorem constantCoeffFourBlock_evaluatedFamilyHessianFourBlock
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (point : Fin 4 → K) :
    constantCoeffFourBlock (evaluatedFamilyHessianFourBlock rho P point) =
      GeneralFourBlock.ofSymmetricMatrix
        (fun i j =>
          mvHessianComponentAt point (polynomialFamilySpecialFiber P)
            (rho i) (rho j)) := by
  ext <;>
    simp [constantCoeffFourBlock, evaluatedFamilyHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, evaluatedFamilyHessian_coeff_zero]

/-- In the right rigid chart, entrywise constant-coefficient specialisation is
exactly the scalar right Hessian block.  The four concrete permutation simp
lemmas reduce this proof before any Schur expression is formed. -/
theorem constantCoeff_rigidExposureRightFourBlock
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    constantCoeffFourBlock (rigidExposureRightFourBlock P) =
      rigidPacketRightHessianBlock D (polynomialFamilySpecialFiber P) := by
  calc
    constantCoeffFourBlock (rigidExposureRightFourBlock P) =
        GeneralFourBlock.ofSymmetricMatrix
          (fun i j =>
            mvHessianComponentAt rigidRightChartPoint
              (polynomialFamilySpecialFiber P)
              (rigidRightChartPerm i) (rigidRightChartPerm j)) := by
      simpa [rigidExposureRightFourBlock] using
        (constantCoeffFourBlock_evaluatedFamilyHessianFourBlock
          rigidRightChartPerm P rigidRightChartPoint)
    _ = rigidPacketRightHessianBlock D
          (polynomialFamilySpecialFiber P) := by
      ext <;>
        simp [GeneralFourBlock.ofSymmetricMatrix,
          rigidPacketRightHessianBlock, rigidRightChartPoint]

/-! ## Constant fibre of the two evaluated charts -/

/-- Constant coefficients of the left evaluated block recover the scalar
left Hessian block of the special fibre. -/
theorem rigidExposureLeftFourBlock_activeDet_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureLeftFourBlock P).activeDet.coeff 0 =
      (rigidPacketLeftHessianBlock D
        (polynomialFamilySpecialFiber P)).activeDet := by
  simp [rigidExposureLeftFourBlock,
    evaluatedFamilyHessianFourBlock,
    GeneralFourBlock.ofSymmetricMatrix,
    GeneralFourBlock.activeDet,
    rigidPacketLeftHessianBlock,
    rigidLeftChartPoint,
    evaluatedFamilyHessian_coeff_zero]

/-- The first cleared Schur coefficient also specialises entrywise. -/
theorem rigidExposureLeftFourBlock_schurA_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureLeftFourBlock P).schurA.coeff 0 =
      (rigidPacketLeftHessianBlock D
        (polynomialFamilySpecialFiber P)).schurA := by
  simp [rigidExposureLeftFourBlock,
    evaluatedFamilyHessianFourBlock,
    GeneralFourBlock.ofSymmetricMatrix,
    GeneralFourBlock.schurA, GeneralFourBlock.activeDet,
    rigidPacketLeftHessianBlock,
    rigidLeftChartPoint,
    evaluatedFamilyHessian_coeff_zero]

/-- Off-diagonal cleared Schur specialisation in the left chart. -/
theorem rigidExposureLeftFourBlock_schurB_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureLeftFourBlock P).schurB.coeff 0 =
      (rigidPacketLeftHessianBlock D
        (polynomialFamilySpecialFiber P)).schurB := by
  simp [rigidExposureLeftFourBlock,
    evaluatedFamilyHessianFourBlock,
    GeneralFourBlock.ofSymmetricMatrix,
    GeneralFourBlock.schurB, GeneralFourBlock.activeDet,
    rigidPacketLeftHessianBlock,
    rigidLeftChartPoint,
    evaluatedFamilyHessian_coeff_zero]

/-- Kernel cleared Schur specialisation in the left chart. -/
theorem rigidExposureLeftFourBlock_schurC_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureLeftFourBlock P).schurC.coeff 0 =
      (rigidPacketLeftHessianBlock D
        (polynomialFamilySpecialFiber P)).schurC := by
  simp [rigidExposureLeftFourBlock,
    evaluatedFamilyHessianFourBlock,
    GeneralFourBlock.ofSymmetricMatrix,
    GeneralFourBlock.schurC, GeneralFourBlock.activeDet,
    rigidPacketLeftHessianBlock,
    rigidLeftChartPoint,
    evaluatedFamilyHessian_coeff_zero]

/-- Constant coefficients of the right evaluated block recover the scalar
right Hessian block of the special fibre. -/
theorem rigidExposureRightFourBlock_activeDet_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureRightFourBlock P).activeDet.coeff 0 =
      (rigidPacketRightHessianBlock D
        (polynomialFamilySpecialFiber P)).activeDet := by
  calc
    (rigidExposureRightFourBlock P).activeDet.coeff 0 =
        (constantCoeffFourBlock (rigidExposureRightFourBlock P)).activeDet :=
      constantCoeffFourBlock_activeDet _
    _ = (rigidPacketRightHessianBlock D
          (polynomialFamilySpecialFiber P)).activeDet := by
      rw [constantCoeff_rigidExposureRightFourBlock (D := D)]

/-- Cleared Schur specialisation in the right chart. -/
theorem rigidExposureRightFourBlock_schurA_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureRightFourBlock P).schurA.coeff 0 =
      (rigidPacketRightHessianBlock D
        (polynomialFamilySpecialFiber P)).schurA := by
  calc
    (rigidExposureRightFourBlock P).schurA.coeff 0 =
        (constantCoeffFourBlock (rigidExposureRightFourBlock P)).schurA :=
      constantCoeffFourBlock_schurA _
    _ = (rigidPacketRightHessianBlock D
          (polynomialFamilySpecialFiber P)).schurA := by
      rw [constantCoeff_rigidExposureRightFourBlock (D := D)]

/-- Off-diagonal cleared Schur specialisation in the right chart. -/
theorem rigidExposureRightFourBlock_schurB_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureRightFourBlock P).schurB.coeff 0 =
      (rigidPacketRightHessianBlock D
        (polynomialFamilySpecialFiber P)).schurB := by
  calc
    (rigidExposureRightFourBlock P).schurB.coeff 0 =
        (constantCoeffFourBlock (rigidExposureRightFourBlock P)).schurB :=
      constantCoeffFourBlock_schurB _
    _ = (rigidPacketRightHessianBlock D
          (polynomialFamilySpecialFiber P)).schurB := by
      rw [constantCoeff_rigidExposureRightFourBlock (D := D)]

/-- Kernel cleared Schur specialisation in the right chart. -/
theorem rigidExposureRightFourBlock_schurC_coeff_zero
    {D : ℕ}
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (rigidExposureRightFourBlock P).schurC.coeff 0 =
      (rigidPacketRightHessianBlock D
        (polynomialFamilySpecialFiber P)).schurC := by
  calc
    (rigidExposureRightFourBlock P).schurC.coeff 0 =
        (constantCoeffFourBlock (rigidExposureRightFourBlock P)).schurC :=
      constantCoeffFourBlock_schurC _
    _ = (rigidPacketRightHessianBlock D
          (polynomialFamilySpecialFiber P)).schurC := by
      rw [constantCoeff_rigidExposureRightFourBlock (D := D)]

/-! ## Exact zero-Schur data from the defect-preserving exposure -/

/-- The left-pivot rigid packet supplies the exact polynomial four-block
expected by the green two-stage zero-Schur clock. -/
noncomputable def CanonicalSmithDepartureFrontier.rigidLeftZeroSchurData
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 D f.lossless.packet)
    (hleft :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).LeftPivot)
    (hD : 3 ≤ D) :
    ExactZeroSchurFourBlockData K := by
  have hchart :=
    rigidPacket_left_zeroSchurChart
      f.lossless.persistentPacket hrigid hleft hD
  refine {
    block := rigidExposureLeftFourBlock f.defectSmithExposureFamily
    defect := alignedSmithRamificationIndex * f.defect
    fullDet := ?_
    activeDet_coeff_zero_ne_zero := ?_
    schurA_coeff_zero := ?_
    schurB_coeff_zero := ?_
    schurC_coeff_zero := ?_
  }
  · exact evaluatedFamilyHessianFourBlock_determinantCore_eq_X_pow
      (Equiv.refl (Fin 4)) f.defectSmithExposureFamily rigidLeftChartPoint
      f.defectSmithExposure_hessianDefect
  · rw [rigidExposureLeftFourBlock_activeDet_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.1
  · rw [rigidExposureLeftFourBlock_schurA_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.2.1
  · rw [rigidExposureLeftFourBlock_schurB_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.2.2.1
  · rw [rigidExposureLeftFourBlock_schurC_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.2.2.2

/-- Right-axis version of the exact zero-Schur constructor. -/
noncomputable def CanonicalSmithDepartureFrontier.rigidRightZeroSchurData
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hrigid : HasRigidRankOnePacket
      (0 : Fin 4) 1 2 D f.lossless.packet)
    (hright :
      (rankOnePacketQuadraticBlock
        (0 : Fin 4) 1 2 D f.lossless.packet).RightAxisPivot)
    (hD : 3 ≤ D) :
    ExactZeroSchurFourBlockData K := by
  have hchart :=
    rigidPacket_right_zeroSchurChart
      f.lossless.persistentPacket hright hD
  refine {
    block := rigidExposureRightFourBlock f.defectSmithExposureFamily
    defect := alignedSmithRamificationIndex * f.defect
    fullDet := ?_
    activeDet_coeff_zero_ne_zero := ?_
    schurA_coeff_zero := ?_
    schurB_coeff_zero := ?_
    schurC_coeff_zero := ?_
  }
  · exact evaluatedFamilyHessianFourBlock_determinantCore_eq_X_pow
      rigidRightChartPerm f.defectSmithExposureFamily rigidRightChartPoint
      f.defectSmithExposure_hessianDefect
  · rw [rigidExposureRightFourBlock_activeDet_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.1
  · rw [rigidExposureRightFourBlock_schurA_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.2.1
  · rw [rigidExposureRightFourBlock_schurB_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.2.2.1
  · rw [rigidExposureRightFourBlock_schurC_coeff_zero (D := D)]
    rw [f.specialFiber_defectSmithExposure_eq_packet]
    exact hchart.2.2.2

/-- The closing predicate carried by one exact zero-Schur four-block. -/
def ExactZeroSchurClosingOutcome
    (B : ExactZeroSchurFourBlockData K) : Prop :=
  (B.toClock.residualDefect = 0 ∧
    B.toClock.tailSeries.active.coeff 0 *
        B.toClock.tailSeries.kernel.coeff 0 -
      B.toClock.tailSeries.offDiag.coeff 0 *
        B.toClock.tailSeries.offDiag.coeff 0 ≠ 0) ∨
  (∃ S : ExactRankOneSchurClockAt K,
    0 < B.toClock.residualDefect ∧
    S.defect = B.toClock.residualDefect ∧
    S.firstOrder = S.defect ∧
    (S.series.offDiag.coeff S.defect ≠ 0 ∨
     S.series.kernel.coeff S.defect ≠ 0))

/-- Closing data produced by the green two-stage zero-Schur clock.
This legacy/existential view is retained for compatibility. -/
def HasRigidTwoStageClosingOutcome
    (complexity : ℕ) : Prop :=
  ∃ B : ExactZeroSchurFourBlockData K, ExactZeroSchurClosingOutcome B

/-- **Frontier-relative rigid closing certificate.**

Unlike `HasRigidTwoStageClosingOutcome`, this certificate does not erase the
geometric origin of the matrix clock.  It remembers the actual canonical
Smith frontier, rigid packet, pivot chart, the exact zero-Schur four-block
constructed from the defect-preserving family, and the closing proof for
that very block.

This is the correct input for the remaining associated-graded terminal
extraction: no later theorem has to guess which family/chart generated an
existential matrix certificate. -/
inductive CanonicalSmithDepartureFrontier.RigidClosingCertificate
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity) : Prop
  | left
      (hD : 3 ≤ D)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D f.lossless.packet)
      (hpivot :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 D f.lossless.packet).LeftPivot)
      (hclosing :
        ExactZeroSchurClosingOutcome (f.rigidLeftZeroSchurData hrigid hpivot hD)) :
      f.RigidClosingCertificate
  | right
      (hD : 3 ≤ D)
      (hrigid : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 D f.lossless.packet)
      (hpivot :
        (rankOnePacketQuadraticBlock
          (0 : Fin 4) 1 2 D f.lossless.packet).RightAxisPivot)
      (hclosing :
        ExactZeroSchurClosingOutcome (f.rigidRightZeroSchurData hrigid hpivot hD)) :
      f.RigidClosingCertificate

/-- Forget the geometric origin of a frontier-relative closing certificate. -/
theorem CanonicalSmithDepartureFrontier.RigidClosingCertificate.toLegacy
    [CharZero K]
    {D complexity : ℕ}
    {f : CanonicalSmithDepartureFrontier (K := K) D complexity}
    (hclose : f.RigidClosingCertificate) :
    HasRigidTwoStageClosingOutcome (K := K) complexity := by
  cases hclose with
  | left hD hrigid hpivot hclosing =>
      exact ⟨f.rigidLeftZeroSchurData hrigid hpivot hD, hclosing⟩
  | right hD hrigid hpivot hclosing =>
      exact ⟨f.rigidRightZeroSchurData hrigid hpivot hD, hclosing⟩

/-- **Rigid branch exhausted above the quadratic boundary.**
For every retained frontier of ordinary degree at least three, the canonical
Smith outcome gives either immediate rank-two progress or the precise
closing data produced by the two-stage Schur clock. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_rigidClosing_of_three_le
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 3 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      HasRigidTwoStageClosingOutcome (K := K) complexity := by
  rcases f.rankTwoProgress_or_rigidDefectExposure with hrepair | hrigid
  · exact Or.inl hrepair.2.1
  · rcases hrigid with ⟨hrigid, _hdef, _hspecial⟩
    rcases f.rigidPacket_pivot hrigid with hleft | hright
    · let B := f.rigidLeftZeroSchurData hrigid hleft hD
      rcases B.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inl hprogress
      · exact Or.inr ⟨B, hclosing⟩
    · let B := f.rigidRightZeroSchurData hrigid hright hD
      rcases B.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inl hprogress
      · exact Or.inr ⟨B, hclosing⟩

/-- **Rigid branch exhausted above the quadratic boundary without losing
geometric provenance.**  This is the restart-facing form to use from now on. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_rigidClosingCertificate_of_three_le
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 3 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      f.RigidClosingCertificate := by
  rcases f.rankTwoProgress_or_rigidDefectExposure with hrepair | hrigid
  · exact Or.inl hrepair.2.1
  · rcases hrigid with ⟨hrigid, _hdef, _hspecial⟩
    rcases f.rigidPacket_pivot hrigid with hleft | hright
    · let B := f.rigidLeftZeroSchurData hrigid hleft hD
      rcases B.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inl hprogress
      · exact Or.inr (.left hD hrigid hleft hclosing)
    · let B := f.rigidRightZeroSchurData hrigid hright hD
      rcases B.rankTwoProgress_or_closing complexity with hprogress | hclosing
      · exact Or.inl hprogress
      · exact Or.inr (.right hD hrigid hright hclosing)

/-- **Exact remaining degree split.**
The current frontier retains `2 ≤ D`, while the handwritten first-wall
statement has positive longitudinal exponent.  Without smuggling that
positivity into the Lean state, the rigorous result is: either the unique
boundary `D=2` remains, or the entire rigid branch is already reduced to
rank-two progress / determinant closing. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_degreeTwo_or_rigidClosing
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      D = 2 ∨
      HasRigidTwoStageClosingOutcome (K := K) complexity := by
  by_cases h2 : D = 2
  · exact Or.inr (Or.inl h2)
  · have h3 : 3 ≤ D := by omega
    rcases f.rankTwoProgress_or_rigidClosing_of_three_le h3 with
      hprogress | hclosing
    · exact Or.inl hprogress
    · exact Or.inr (Or.inr hclosing)

/-- **The quadratic departure frontier is impossible.**
The full family homogeneity retained by the departure frontier turns the
`D = 2` boundary into a linear-gradient problem over the coefficient domain
`K[X]`.  The exact Hessian clock is a nonzero polynomial, so the quadratic
gradient is injective and the two moving collision sections must coincide.
Their specialisations are the distinct canonical points `0` and `e₀`, a
contradiction. -/
theorem CanonicalSmithDepartureFrontier.degree_two_impossible
    [CharZero K]
    {complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) 2 complexity) :
    False := by
  have hsections :
      f.lossless.leftSection = f.lossless.rightSection :=
    quadraticPolynomialFamily_exactCollision_sections_eq
      f.lossless.family
      f.homogeneous
      f.lossless.leftSection
      f.lossless.rightSection
      f.hessianDefect
      f.lossless.exactCollision
  have hspecial :=
    congrArg polynomialSectionSpecialPoint hsections
  rw [f.lossless.leftSpecial, f.lossless.rightSpecial] at hspecial
  exact
    coordinateAxisPoint_zero_ne_zeroPoint (K := K) hspecial.symm

/-- **Rigid Smith branch with no degree boundary.**
For every retained degree `D ≥ 2`, the canonical Smith frontier now yields
either strict rank-two repair progress or the precise two-stage
determinant-closing data.  The previously isolated `D = 2` branch is ruled
out intrinsically by quadratic gradient injectivity. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_rigidClosing
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      HasRigidTwoStageClosingOutcome (K := K) complexity := by
  rcases
      f.rankTwoProgress_or_degreeTwo_or_rigidClosing hD with
    hprogress | h2 | hclosing
  · exact Or.inl hprogress
  · subst D
    exact (f.degree_two_impossible).elim
  · exact Or.inr hclosing

/-- **All-degree rigid closing theorem with retained provenance.**
For every canonical departure frontier of degree at least two, either strict
rank-two repair progress occurs or the closing certificate remembers the
actual frontier/family/chart that generated it.  The quadratic boundary is
eliminated by `degree_two_impossible`. -/
theorem CanonicalSmithDepartureFrontier.rankTwoProgress_or_rigidClosingCertificate
    [CharZero K]
    {D complexity : ℕ}
    (f : CanonicalSmithDepartureFrontier (K := K) D complexity)
    (hD : 2 ≤ D) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∨
      f.RigidClosingCertificate := by
  by_cases h2 : D = 2
  · subst D
    exact (f.degree_two_impossible).elim
  · have h3 : 3 ≤ D := by omega
    exact f.rankTwoProgress_or_rigidClosingCertificate_of_three_le h3

end

end HC4.Valuation
