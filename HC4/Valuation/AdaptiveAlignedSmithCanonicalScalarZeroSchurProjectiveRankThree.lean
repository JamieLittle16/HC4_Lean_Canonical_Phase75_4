import HC4.Valuation.AdaptiveAlignedSmithCanonicalScalarZeroSchurRankThree
import Mathlib.Tactic

/-!
# A18.4.80: scalar zero-Schur projective closing is rank-three geometry

A18.4.79 leaves only the positive-residual exact closing clock.  The A17.16
calculation already identifies what that branch means geometrically.  The
first normalised Schur tail is a nonzero determinant-zero binary block, hence
has a canonical one-dimensional kernel.  At exact residual closing, the later
raw Schur coefficient evaluates nontrivially in that kernel direction.

For an already-rank-two packet this is exactly a new independent projective
direction.  We therefore retain the denominator-free raw departure coefficient
and only then attach the canonical rank-two -> rank-three repair promotion.

The scalar coefficient field makes the argument cleaner than A17.16: no source
evaluation is necessary.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Physical raw-Schur order of the canonical residual closing layer. -/
def scalarZeroSchurResidualPhysicalOrder
    (Z : ExactZeroSchurFourBlockData K) : ℕ :=
  Z.toClock.firstOrder + Z.toClock.residualDefect

/-- Left-pivot kernel-direction departure coefficient on the original raw
zero-Schur series. -/
noncomputable def scalarZeroSchurLeftRawDeparture
    (Z : ExactZeroSchurFourBlockData K) : K :=
  let E := Z.toClock
  let S := E.zeroSeries.series
  let e := E.firstOrder
  let n := scalarZeroSchurResidualPhysicalOrder Z
  (S.offDiag.coeff e)^2 * S.active.coeff n -
    2 * S.active.coeff e * S.offDiag.coeff e * S.offDiag.coeff n +
    (S.active.coeff e)^2 * S.kernel.coeff n

/-- Right-axis analogue. -/
noncomputable def scalarZeroSchurRightRawDeparture
    (Z : ExactZeroSchurFourBlockData K) : K :=
  Z.toClock.zeroSeries.series.active.coeff
    (scalarZeroSchurResidualPhysicalOrder Z)

/-- Tail-to-raw coefficient transport, now over the scalar field. -/
theorem ExactZeroSchurClock.scalar_active_coeff_firstOrder_add_eq_tail
    (E : ExactZeroSchurClock K)
    (r : ℕ) :
    E.zeroSeries.series.active.coeff (E.firstOrder + r) =
      E.tailSeries.active.coeff r := by
  change
    E.zeroSeries.series.active.coeff
        (E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer + r) =
      (E.zeroSeries.tailSeries E.hasPositiveEntryLayer).active.coeff r
  rw [E.zeroSeries.active_eq_firstFactor_mul_tail E.hasPositiveEntryLayer]
  rw [Polynomial.coeff_X_pow_mul']
  simp [ZeroSchurSeries.tailSeries]

theorem ExactZeroSchurClock.scalar_offDiag_coeff_firstOrder_add_eq_tail
    (E : ExactZeroSchurClock K)
    (r : ℕ) :
    E.zeroSeries.series.offDiag.coeff (E.firstOrder + r) =
      E.tailSeries.offDiag.coeff r := by
  change
    E.zeroSeries.series.offDiag.coeff
        (E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer + r) =
      (E.zeroSeries.tailSeries E.hasPositiveEntryLayer).offDiag.coeff r
  rw [E.zeroSeries.offDiag_eq_firstFactor_mul_tail E.hasPositiveEntryLayer]
  rw [Polynomial.coeff_X_pow_mul']
  simp [ZeroSchurSeries.tailSeries]

theorem ExactZeroSchurClock.scalar_kernel_coeff_firstOrder_add_eq_tail
    (E : ExactZeroSchurClock K)
    (r : ℕ) :
    E.zeroSeries.series.kernel.coeff (E.firstOrder + r) =
      E.tailSeries.kernel.coeff r := by
  change
    E.zeroSeries.series.kernel.coeff
        (E.zeroSeries.firstPositiveEntryOrder E.hasPositiveEntryLayer + r) =
      (E.zeroSeries.tailSeries E.hasPositiveEntryLayer).kernel.coeff r
  rw [E.zeroSeries.kernel_eq_firstFactor_mul_tail E.hasPositiveEntryLayer]
  rw [Polynomial.coeff_X_pow_mul']
  simp [ZeroSchurSeries.tailSeries]

/-- The residual physical closing layer is strictly before the outer
zero-Schur determinant clock. -/
theorem ExactZeroSchurClock.scalar_firstOrder_add_residualDefect_lt_defect
    (E : ExactZeroSchurClock K) :
    E.firstOrder + E.residualDefect < E.defect := by
  have hle := E.twice_firstOrder_le_defect
  have hpos := E.firstOrder_pos
  unfold ExactZeroSchurClock.residualDefect
  omega

/-- Exact rank-one residual closure necessarily has nonzero kernel
coefficient at closing order. -/
theorem exactScalarRankOneSchurClock_kernel_coeff_defect_ne_zero_of_closing
    (S : ExactRankOneSchurClockAt K)
    (hclose : S.firstOrder = S.defect) :
    S.series.kernel.coeff S.defect ≠ 0 := by
  have hdet : S.series.determinant.coeff S.defect ≠ 0 := by
    rw [S.determinantFactor]
    rw [Polynomial.coeff_mul_X_pow']
    simpa using S.clearingFactor_coeff_zero_ne_zero
  have hlin :
      S.series.determinant.coeff S.firstOrder =
        S.series.leading * S.series.kernel.coeff S.firstOrder := by
    simpa [FirstRankOneSchurDeparture.determinant,
      RankOneSchurSeries.determinant, ExactRankOneSchurClockAt.firstOrder] using
      (S.series.firstDeparture S.hasTransverse).coeff_order_determinant
  have hkernelFirst : S.series.kernel.coeff S.firstOrder ≠ 0 := by
    intro hz
    apply hdet
    rw [← hclose, hlin, hz]
    simp
  simpa [hclose] using hkernelFirst

/-- Geometry carried by a scalar projective closing event on an already
rank-two packet. -/
inductive AdaptiveAlignedSmithCanonicalScalarProjectiveRankThreeExit
    (Z : ExactZeroSchurFourBlockData K)
    (complexity : ℕ) : Prop
  | left
      (hres : 0 < Z.toClock.residualDefect)
      (hleft : Z.toClock.tailSeries.LeftPivot)
      (rawDeparture_ne : scalarZeroSchurLeftRawDeparture Z ≠ 0)
      (physicalOrder_lt :
        scalarZeroSchurResidualPhysicalOrder Z < Z.toClock.defect)
      (rankTwoToRankThree :
        RepairProgress
          (rankTwoRepairState complexity)
          (rankThreeRepairState complexity))
      (measure_lt :
        (rankThreeRepairState complexity).measure <
          (rankTwoRepairState complexity).measure)
  | right
      (hres : 0 < Z.toClock.residualDefect)
      (hright : Z.toClock.tailSeries.RightAxisPivot)
      (rawDeparture_ne : scalarZeroSchurRightRawDeparture Z ≠ 0)
      (physicalOrder_lt :
        scalarZeroSchurResidualPhysicalOrder Z < Z.toClock.defect)
      (rankTwoToRankThree :
        RepairProgress
          (rankTwoRepairState complexity)
          (rankThreeRepairState complexity))
      (measure_lt :
        (rankThreeRepairState complexity).measure <
          (rankTwoRepairState complexity).measure)

/-- Complete scalar zero-Schur rank-three geometry: either a single
nondegenerate binary block, or a later coefficient leaving the kernel line of
the first rank-one Schur tail. -/
inductive AdaptiveAlignedSmithCanonicalCompleteScalarRankThreeGeometry
    (Z : ExactZeroSchurFourBlockData K)
    (complexity : ℕ) : Type (u + 1)
  | nondegenerate
      (E : AdaptiveAlignedSmithCanonicalScalarNondegenerateRankThreeExit
        (K := K) complexity)
  | projective
      (E : AdaptiveAlignedSmithCanonicalScalarProjectiveRankThreeExit
        (K := K) Z complexity)

/-- **Every scalar exact zero-Schur packet produces actual rank-three
geometry.** -/
noncomputable def exactScalarZeroSchur_completeRankThreeGeometry
    (Z : ExactZeroSchurFourBlockData K)
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalCompleteScalarRankThreeGeometry
      Z complexity := by
  let E := Z.toClock
  by_cases hres0 : E.residualDefect = 0
  · exact .nondegenerate
      (scalarRankThreeExit_of_residualZero Z complexity hres0)
  · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
    have hphysical : E.firstOrder + E.residualDefect < E.defect :=
      E.scalar_firstOrder_add_residualDefect_lt_defect
    rcases E.tail_pivot_of_residual_pos hres with hleft | hright
    · let S := E.toRankOneClockLeft hres hleft
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · exact .nondegenerate
          (scalarRankThreeExit_of_preterminal S complexity hpre)
      · have hkernelS : S.series.kernel.coeff S.defect ≠ 0 :=
          exactScalarRankOneSchurClock_kernel_coeff_defect_ne_zero_of_closing
            S hclose
        have hkernel :
            (E.toRankOneClockLeft hres hleft).series.kernel.coeff
              E.residualDefect ≠ 0 := by
          simpa [S, ExactZeroSchurClock.toRankOneClockLeft] using hkernelS
        have haligned :
            (E.tailSeries.alignLeft hleft).kernel.coeff E.residualDefect ≠ 0 := by
          simpa [ExactZeroSchurClock.toRankOneClockLeft] using hkernel
        have hraw :
            (E.tailSeries.offDiag.coeff 0)^2 *
                  E.tailSeries.active.coeff E.residualDefect -
                2 * E.tailSeries.active.coeff 0 *
                  E.tailSeries.offDiag.coeff 0 *
                  E.tailSeries.offDiag.coeff E.residualDefect +
                (E.tailSeries.active.coeff 0)^2 *
                  E.tailSeries.kernel.coeff E.residualDefect ≠ 0 := by
          rw [E.tailSeries.alignLeft_kernel_coeff hleft E.residualDefect] at haligned
          exact haligned
        have hA0 :
            E.tailSeries.active.coeff 0 =
              E.zeroSeries.series.active.coeff E.firstOrder := by
          symm
          simpa using E.scalar_active_coeff_firstOrder_add_eq_tail 0
        have hB0 :
            E.tailSeries.offDiag.coeff 0 =
              E.zeroSeries.series.offDiag.coeff E.firstOrder := by
          symm
          simpa using E.scalar_offDiag_coeff_firstOrder_add_eq_tail 0
        have hAr :
            E.tailSeries.active.coeff E.residualDefect =
              E.zeroSeries.series.active.coeff
                (E.firstOrder + E.residualDefect) := by
          symm
          exact E.scalar_active_coeff_firstOrder_add_eq_tail E.residualDefect
        have hBr :
            E.tailSeries.offDiag.coeff E.residualDefect =
              E.zeroSeries.series.offDiag.coeff
                (E.firstOrder + E.residualDefect) := by
          symm
          exact E.scalar_offDiag_coeff_firstOrder_add_eq_tail E.residualDefect
        have hCr :
            E.tailSeries.kernel.coeff E.residualDefect =
              E.zeroSeries.series.kernel.coeff
                (E.firstOrder + E.residualDefect) := by
          symm
          exact E.scalar_kernel_coeff_firstOrder_add_eq_tail E.residualDefect
        rw [hA0, hB0, hAr, hBr, hCr] at hraw
        have hrepair := rankTwo_to_rankThree_repairProgress complexity
        exact .projective <| .left
          (by simpa [E] using hres)
          (by simpa [E] using hleft)
          (by
            simpa [scalarZeroSchurLeftRawDeparture,
              scalarZeroSchurResidualPhysicalOrder, E] using hraw)
          (by
            simpa [scalarZeroSchurResidualPhysicalOrder, E] using hphysical)
          hrepair (repairState_measure_lt_of_progress hrepair)
    · let S := E.toRankOneClockRight hres hright
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · exact .nondegenerate
          (scalarRankThreeExit_of_preterminal S complexity hpre)
      · have hkernelS : S.series.kernel.coeff S.defect ≠ 0 :=
          exactScalarRankOneSchurClock_kernel_coeff_defect_ne_zero_of_closing
            S hclose
        have hkernel :
            (E.toRankOneClockRight hres hright).series.kernel.coeff
              E.residualDefect ≠ 0 := by
          simpa [S, ExactZeroSchurClock.toRankOneClockRight] using hkernelS
        have haligned :
            (E.tailSeries.alignRight hright).kernel.coeff E.residualDefect ≠ 0 := by
          simpa [ExactZeroSchurClock.toRankOneClockRight] using hkernel
        have hraw : E.tailSeries.active.coeff E.residualDefect ≠ 0 := by
          simpa [BinarySchurPolynomialSeries.alignRight] using haligned
        have hAr :
            E.tailSeries.active.coeff E.residualDefect =
              E.zeroSeries.series.active.coeff
                (E.firstOrder + E.residualDefect) := by
          symm
          exact E.scalar_active_coeff_firstOrder_add_eq_tail E.residualDefect
        rw [hAr] at hraw
        have hrepair := rankTwo_to_rankThree_repairProgress complexity
        exact .projective <| .right
          (by simpa [E] using hres)
          (by simpa [E] using hright)
          (by
            simpa [scalarZeroSchurRightRawDeparture,
              scalarZeroSchurResidualPhysicalOrder, E] using hraw)
          (by
            simpa [scalarZeroSchurResidualPhysicalOrder, E] using hphysical)
          hrepair (repairState_measure_lt_of_progress hrepair)

end

end HC4.Valuation
