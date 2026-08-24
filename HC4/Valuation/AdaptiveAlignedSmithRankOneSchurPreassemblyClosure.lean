import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurRawBinaryProjectiveLine
import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockStationaryEndgame
import HC4.Newton.RankOnePacketReentry
import Mathlib.Tactic

/-!
# Stage 4B38: raw Schur derivative repair and preassembly closure

The previous projective filtration isolates the correct raw binary Schur line,
but the moving-line branch admits a shorter source-honest closure which does
not require another RS2 coefficient extraction.

Write the special rank-one Schur block as

    S = [[A, B], [B, C]],    A*C = B^2.

For every honest source derivative `d_k`, differentiating the rank-one
relation and eliminating `C` gives the exact identity

    A^2 * det(d_k S) = -(A * d_k B - B * d_k A)^2.

Thus a nonzero raw projective wedge forces the derivative Schur block to have
nonzero determinant.  We retain that determinant as a polynomial source,
choose an actual source point where it is nonzero, and package the resulting
field-valued binary block with trivial kernel.  This is the concrete rank-two
certificate accompanying the already-green canonical rank-one -> rank-two
`RepairProgress`.

The complementary branch is exactly B32's constant raw binary Schur line.
For an early-Schur first-key context we additionally retain the already-green
B30 provenance packet built from that constant line.

The final theorem upgrades the moving branch immediately to the exact-clock
outer rank-two macro.  Consequently the output of this file is deliberately
an assembly interface:

    sound rank-two outer macro
      OR
    constant raw Schur line + canonical first-key provenance.

No new filtration, clock identification, projective lift, or termination
measure is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-! ## The special raw Schur block is rank one -/

private theorem specialFourBlock_schurA_eq_raw_coeff_zero_B38
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.specialFourBlock.schurA =
      C.chartData.schurData.block.polynomialSchurSeries.active.coeff 0 := by
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.specialFourBlock,
    GeneralFourBlock.polynomialSchurSeries] using
    (parameterConstantCoeffFourBlock_schurA C.chartData.schurData.block).symm

private theorem specialFourBlock_schurB_eq_raw_coeff_zero_B38
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.specialFourBlock.schurB =
      C.chartData.schurData.block.polynomialSchurSeries.offDiag.coeff 0 := by
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.specialFourBlock,
    GeneralFourBlock.polynomialSchurSeries] using
    (parameterConstantCoeffFourBlock_schurB C.chartData.schurData.block).symm

private theorem specialFourBlock_schurC_eq_raw_coeff_zero_B38
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.specialFourBlock.schurC =
      C.chartData.schurData.block.polynomialSchurSeries.kernel.coeff 0 := by
  simpa [AdaptiveAlignedSmithRankOneClosingSourceCarrier.specialFourBlock,
    GeneralFourBlock.polynomialSchurSeries] using
    (parameterConstantCoeffFourBlock_schurC C.chartData.schurData.block).symm

/-- The retained special binary Schur block satisfies the rank-one determinant
relation as an identity in the honest source polynomial ring. -/
theorem specialFourBlock_rawSchur_rankOne
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.specialFourBlock.schurA * C.specialFourBlock.schurC =
      C.specialFourBlock.schurB * C.specialFourBlock.schurB := by
  have hA := C.specialFourBlock_schurA_eq_raw_coeff_zero_B38
  have hB := C.specialFourBlock_schurB_eq_raw_coeff_zero_B38
  have hC := C.specialFourBlock_schurC_eq_raw_coeff_zero_B38
  generalize hp : C.chartData.schurData.chosenPivot = p
  cases p with
  | left hleft =>
      rw [hA, hB, hC]
      exact hleft.2
  | right hright =>
      rw [hA, hB, hC, hright.1, hright.2.1]
      simp

/-! ## Differentiate the rank-one determinant -/

/-- Determinant of the honest source derivative of the raw special Schur
block in source direction `k`. -/
def rawSpecialSchurDerivativeDet
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4) : MvPolynomial (Fin 4) K :=
  MvPolynomial.pderiv k C.specialFourBlock.schurA *
      MvPolynomial.pderiv k C.specialFourBlock.schurC -
    MvPolynomial.pderiv k C.specialFourBlock.schurB *
      MvPolynomial.pderiv k C.specialFourBlock.schurB

/-- **Negative-square derivative identity.**

For a rank-one symmetric binary block `A*C = B^2`, the determinant of its
source derivative satisfies

    A^2 det(dS) = -(A dB - B dA)^2.

This is the direct rank-two source exposed by nonconstant raw Schur motion. -/
theorem rawSpecialSchurDerivativeDet_negativeSquare
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4) :
    C.specialFourBlock.schurA ^ 2 * C.rawSpecialSchurDerivativeDet k =
      -(C.rawSpecialSchurProjectiveWedge k) ^ 2 := by
  let A : MvPolynomial (Fin 4) K := C.specialFourBlock.schurA
  let M : MvPolynomial (Fin 4) K := C.specialFourBlock.schurB
  let N : MvPolynomial (Fin 4) K := C.specialFourBlock.schurC
  let Ap : MvPolynomial (Fin 4) K := MvPolynomial.pderiv k A
  let Mp : MvPolynomial (Fin 4) K := MvPolynomial.pderiv k M
  let Np : MvPolynomial (Fin 4) K := MvPolynomial.pderiv k N

  have hdet : A * N = M * M := by
    simpa [A, M, N] using C.specialFourBlock_rawSchur_rankOne

  have hdiff : Ap * N + A * Np = Mp * M + M * Mp := by
    have h := congrArg (MvPolynomial.pderiv k) hdet
    have h' : A * Np + N * Ap = M * Mp + M * Mp := by
      simpa [A, M, N, Ap, Mp, Np] using h
    calc
      Ap * N + A * Np = A * Np + N * Ap := by ring
      _ = M * Mp + M * Mp := h'
      _ = Mp * M + M * Mp := by ring

  have hzero :
      A ^ 2 * (Ap * Np - Mp * Mp) + (A * Mp - M * Ap) ^ 2 = 0 := by
    calc
      A ^ 2 * (Ap * Np - Mp * Mp) + (A * Mp - M * Ap) ^ 2 =
          A * Ap *
              ((Ap * N + A * Np) - (Mp * M + M * Mp)) -
            Ap ^ 2 * (A * N - M * M) := by ring
      _ = 0 := by rw [sub_eq_zero.mpr hdiff, sub_eq_zero.mpr hdet]; ring

  change A ^ 2 * (Ap * Np - Mp * Mp) = -(A * Mp - M * Ap) ^ 2
  calc
    A ^ 2 * (Ap * Np - Mp * Mp) =
        (A ^ 2 * (Ap * Np - Mp * Mp) + (A * Mp - M * Ap) ^ 2) -
          (A * Mp - M * Ap) ^ 2 := by ring
    _ = -(A * Mp - M * Ap) ^ 2 := by rw [hzero]; ring

/-- A nonzero raw projective wedge therefore forces the derivative Schur
determinant itself to be a nonzero source polynomial. -/
theorem rawSpecialSchurDerivativeDet_ne_zero_of_wedge
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4)
    (hwedge : C.rawSpecialSchurProjectiveWedge k ≠ 0) :
    C.rawSpecialSchurDerivativeDet k ≠ 0 := by
  intro hdet
  have hneg : -(C.rawSpecialSchurProjectiveWedge k) ^ 2 = 0 := by
    calc
      -(C.rawSpecialSchurProjectiveWedge k) ^ 2 =
          C.specialFourBlock.schurA ^ 2 * C.rawSpecialSchurDerivativeDet k :=
        (C.rawSpecialSchurDerivativeDet_negativeSquare k).symm
      _ = 0 := by rw [hdet]; ring
  have hsq : (C.rawSpecialSchurProjectiveWedge k) ^ 2 = 0 :=
    neg_eq_zero.mp hneg
  exact (pow_ne_zero 2 hwedge) hsq

/-! ## A literal field-valued rank-two block -/

/-- Evaluate the derivative raw Schur block at one honest source point. -/
def rawSpecialSchurDerivativeBlockAt
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4)
    (point : Fin 4 → K) : BinarySchurBlock K where
  a := MvPolynomial.eval point
    (MvPolynomial.pderiv k C.specialFourBlock.schurA)
  b := MvPolynomial.eval point
    (MvPolynomial.pderiv k C.specialFourBlock.schurB)
  c := MvPolynomial.eval point
    (MvPolynomial.pderiv k C.specialFourBlock.schurC)

/-- Evaluation commutes with the binary determinant source. -/
theorem rawSpecialSchurDerivativeBlockAt_detCore
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (k : Fin 4)
    (point : Fin 4 → K) :
    (C.rawSpecialSchurDerivativeBlockAt k point).detCore =
      MvPolynomial.eval point (C.rawSpecialSchurDerivativeDet k) := by
  simp [rawSpecialSchurDerivativeBlockAt,
    rawSpecialSchurDerivativeDet, BinarySchurBlock.detCore]

/-- Concrete moving-line repair packet.  Besides the canonical repair step it
retains the exact negative-square polynomial identity and an actual source
point at which the derivative Schur block is nondegenerate. -/
structure RawSpecialSchurDerivativeRankTwoRepairData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (complexity : ℕ) where
  direction : Fin 4
  wedge_ne_zero : C.rawSpecialSchurProjectiveWedge direction ≠ 0
  derivativeDet_ne_zero : C.rawSpecialSchurDerivativeDet direction ≠ 0
  negativeSquare :
    C.specialFourBlock.schurA ^ 2 *
        C.rawSpecialSchurDerivativeDet direction =
      -(C.rawSpecialSchurProjectiveWedge direction) ^ 2
  point : Fin 4 → K
  point_det_ne_zero :
    MvPolynomial.eval point (C.rawSpecialSchurDerivativeDet direction) ≠ 0
  evaluatedBlock_detCore_ne_zero :
    (C.rawSpecialSchurDerivativeBlockAt direction point).detCore ≠ 0
  evaluatedBlock_trivialKernel :
    (C.rawSpecialSchurDerivativeBlockAt direction point).HasTrivialKernel
  progress :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity)
  measure_lt :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure

/-- Construct the full concrete rank-two repair packet from one nonzero raw
Schur projective wedge. -/
theorem rawSpecialSchurDerivativeRankTwoRepairData_of_wedge
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (complexity : ℕ)
    (k : Fin 4)
    (hwedge : C.rawSpecialSchurProjectiveWedge k ≠ 0) :
    Nonempty (C.RawSpecialSchurDerivativeRankTwoRepairData complexity) := by
  have hdet : C.rawSpecialSchurDerivativeDet k ≠ 0 :=
    C.rawSpecialSchurDerivativeDet_ne_zero_of_wedge k hwedge
  rcases exists_source_eval_ne_zero_of_ne_zero
      (C.rawSpecialSchurDerivativeDet k) hdet with
    ⟨point, hpoint⟩
  have hblock :
      (C.rawSpecialSchurDerivativeBlockAt k point).detCore ≠ 0 := by
    rw [C.rawSpecialSchurDerivativeBlockAt_detCore k point]
    exact hpoint
  have htrivial :
      (C.rawSpecialSchurDerivativeBlockAt k point).HasTrivialKernel :=
    BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero
      (C.rawSpecialSchurDerivativeBlockAt k point) hblock
  have hprogress :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) :=
    rankOne_to_rankTwo_repairProgress complexity
  exact ⟨{
    direction := k
    wedge_ne_zero := hwedge
    derivativeDet_ne_zero := hdet
    negativeSquare := C.rawSpecialSchurDerivativeDet_negativeSquare k
    point := point
    point_det_ne_zero := hpoint
    evaluatedBlock_detCore_ne_zero := hblock
    evaluatedBlock_trivialKernel := htrivial
    progress := hprogress
    measure_lt := repairState_measure_lt_of_progress hprogress
  }⟩

/-! ## Constant-line branch with exact first-key provenance -/

/-- Assembly packet for the genuinely residual stationary branch.

The literal constant binary Schur line is retained together with a B30
first-key provenance packet built from *that exact line*, and the B28/B30
first-key rank-two alternative has already been discharged.  Thus the packet
is genuinely RS2-ready rather than merely carrying an unclassified first key. -/
structure ConstantSpecialSchurKernelLineRS2PreassemblyData
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) where
  line : C.ConstantSpecialSchurKernelLineData
  provenance : C.FirstKeyCanonicalRS2ProvenanceAssemblyData
  provenance_schurKernel :
    provenance.schurKernel = line.toDenominatorClearedSpecialSchurKernelData
  rs2Ready : C.FirstKeyXeLmRS2ReadyData provenance.canonical

/-- Rebuild the B30 packet from a *specified* constant line while retaining
literal equality of the stored Schur kernel with that line's canonical
Stage-3 representative.  This avoids asking final assembly to recover a
provenance equality from an existential theorem. -/
theorem HasFirstTransverseSourceKey.exists_constantLineCanonicalProvenance
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (hkey : C.HasFirstTransverseSourceKey)
    (L : C.ConstantSpecialSchurKernelLineData) :
    ∃ A : C.FirstKeyCanonicalRS2ProvenanceAssemblyData,
      A.schurKernel = L.toDenominatorClearedSpecialSchurKernelData := by
  let E : C.DenominatorClearedSpecialSchurKernelData :=
    L.toDenominatorClearedSpecialSchurKernelData
  rcases hkey.exists_leadingTransverseKernelData_of_schurKernel E with
    ⟨T, hsource⟩
  rcases T.exists_canonicalMaximalHomogeneousKernelData with ⟨D⟩
  rcases T.exists_longitudinalFactorData_unconditional with ⟨F⟩
  let A : C.FirstKeyCanonicalRS2ProvenanceAssemblyData := {
    schurKernel := E
    leading := T
    sourceKernel_eq := hsource
    canonical := D
    factor := F
  }
  exact ⟨A, rfl⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-! ## Exact-clock assembly-facing wrapper -/

namespace AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

/-- **Single preassembly closure for one exact-clock early-Schur problem.**

All rank-two alternatives are consumed here, not deferred to final assembly:

* if the raw binary Schur line moves, the negative-square derivative identity
  supplies a concrete rank-two source and canonical repair progress;
* if the raw line is constant but B30's first key already has a rank-two
  transverse Hessian witness, that existing repair packet is consumed too;
* only the constant-line + RS2-ready packet survives on the right.

The left disjunct is stated with the *unwrapped* certified internal move so it
can be fed directly to the existing `rankTwoMacro` outcome constructor. -/
theorem earlySchur_rankTwoMacro_or_constantLineRS2Preassembly
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (RR : RepairRanking)
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
    (hlt :
      C.firstActualLayerOrder <
        P.stationary.blocker.aligned.endpoint.defect) :
    (∃ outer target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      HasCertifiedRamifiedEpisodeInternalMove outer s ∧
      CertifiedSameScaleEpisodeProgress RR target outer) ∨
      Nonempty C.ConstantSpecialSchurKernelLineRS2PreassemblyData := by
  let X : AdaptiveAlignedSmithEarlySchurFirstKeyContext P C hlt :=
    P.earlySchurFirstKeyContext C hlt
  rcases C.rawSpecialSchurProjectiveWedge_or_constantLine with hmoving | hconstant
  · rcases hmoving with ⟨k, hk⟩
    rcases C.rawSpecialSchurDerivativeRankTwoRepairData_of_wedge
        complexity k hk with ⟨R⟩
    left
    rcases P.stationary.blocker.aligned.exists_outerRankTwoRepairMacro
        RR s complexity hsrepair P.clock_eq R.progress with
      ⟨outer, target, hmove, hprogress⟩
    exact ⟨outer, target, hmove, hprogress⟩
  · rcases hconstant with ⟨L⟩
    rcases X.firstSpatialKey.exists_constantLineCanonicalProvenance L with
      ⟨A, hAE⟩
    rcases A.rankTwoRepair_or_rs2Ready complexity with hrepair | hrs2
    · rcases hrepair with ⟨R⟩
      left
      rcases P.stationary.blocker.aligned.exists_outerRankTwoRepairMacro
          RR s complexity hsrepair P.clock_eq R.repairProgress with
        ⟨outer, target, hmove, hprogress⟩
      exact ⟨outer, target, hmove, hprogress⟩
    · rcases hrs2 with ⟨N⟩
      right
      exact ⟨{
        line := L
        provenance := A
        provenance_schurKernel := hAE
        rs2Ready := N
      }⟩

end AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

end

end HC4.Valuation
