import HC4.Valuation.AdaptiveAlignedSmithCanonicalSourceZeroSchurRankThree
import HC4.Valuation.AdaptiveAlignedSmithExactSchurClock
import Mathlib.Tactic

/-!
# A18.4.86: an adaptive preterminal rank-one Schur clock is already rank three

The historical adaptive Schur interface labelled a preterminal first
transverse layer merely as `rankOne -> rankTwo` repair progress.  The retained
clock contains strictly more geometry.

At its first transverse order below determinant closure,

* the kernel coefficient is identically zero; and
* the off-diagonal coefficient is a nonzero source polynomial.

Evaluate the latter at a source point where it remains nonzero.  The resulting
binary coefficient block has the form

    [ a  b ]
    [ b  0 ]

with `b != 0`, and therefore determinant `-b^2 != 0`.  This is exactly the
nondegenerate residual event used by A17.13 to license the finite
`rankTwo -> rankThree` transition.

The theorem is indexed only by the honest adaptive Schur clock, so every
blocker chart carrying such a clock can reuse it without reconstructing an
auxiliary zero-Schur packet.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Evaluate the first transverse coefficient block of an adaptive rank-one
Schur clock. -/
noncomputable def adaptiveSchurFirstTransverseBlock
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (point : Fin 4 → K) : BinarySchurBlock K where
  a := MvPolynomial.eval point S.series.leading
  b := MvPolynomial.eval point
    (S.series.offDiag.coeff S.firstOrder)
  c := MvPolynomial.eval point
    (S.series.kernel.coeff S.firstOrder)

/-- Concrete nondegenerate event carried by a preterminal adaptive Schur
clock. -/
structure AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThreeExit
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hpre : S.firstOrder < E.defect)
    (complexity : ℕ) where
  point : Fin 4 → K
  offDiag_ne : (adaptiveSchurFirstTransverseBlock S point).b ≠ 0
  kernel_eq_zero : (adaptiveSchurFirstTransverseBlock S point).c = 0
  detCore_ne_zero : (adaptiveSchurFirstTransverseBlock S point).detCore ≠ 0
  trivialKernel : (adaptiveSchurFirstTransverseBlock S point).HasTrivialKernel
  rankTwoToRankThree :
    RepairProgress
      (rankTwoRepairState complexity)
      (rankThreeRepairState complexity)
  measure_lt :
    (rankThreeRepairState complexity).measure <
      (rankTwoRepairState complexity).measure

/-- **Adaptive preterminal Schur geometry is a genuine rank-three exit.** -/
theorem AdaptiveAlignedExactRankOneSchurClock.exists_preterminalRankThreeExit
    {degreeCap : ℕ}
    {E : AdaptiveAlignedSmithMinimalEndpoint (K := K) degreeCap}
    (S : AdaptiveAlignedExactRankOneSchurClock E)
    (hpre : S.firstOrder < E.defect)
    (complexity : ℕ) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalAdaptiveSchurPreterminalRankThreeExit
        S hpre complexity) := by
  let B : MvPolynomial (Fin 4) K :=
    S.series.offDiag.coeff S.firstOrder
  have hB : B ≠ 0 := by
    simpa [B] using S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
  rcases exists_source_eval_ne_zero_of_ne_zero B hB with ⟨point, hpoint⟩
  have hkernelPoly :
      S.series.kernel.coeff S.firstOrder = 0 :=
    S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre
  let q : BinarySchurBlock K := adaptiveSchurFirstTransverseBlock S point
  have hoff : q.b ≠ 0 := by
    simpa [q, adaptiveSchurFirstTransverseBlock, B] using hpoint
  have hkernel : q.c = 0 := by
    simp [q, adaptiveSchurFirstTransverseBlock, hkernelPoly]
  have hdetEq : q.detCore = -(q.b * q.b) := by
    simp [BinarySchurBlock.detCore, hkernel]
  have hdet : q.detCore ≠ 0 := by
    rw [hdetEq]
    exact neg_ne_zero.mpr (mul_ne_zero hoff hoff)
  have htrivial : q.HasTrivialKernel :=
    BinarySchurBlock.hasTrivialKernel_of_detCore_ne_zero q hdet
  have hrepair :
      RepairProgress
        (rankTwoRepairState complexity)
        (rankThreeRepairState complexity) :=
    rankTwo_to_rankThree_repairProgress complexity
  exact ⟨{
    point := point
    offDiag_ne := by simpa [q] using hoff
    kernel_eq_zero := by simpa [q] using hkernel
    detCore_ne_zero := by simpa [q] using hdet
    trivialKernel := by simpa [q] using htrivial
    rankTwoToRankThree := hrepair
    measure_lt := repairState_measure_lt_of_progress hrepair
  }⟩

end

end HC4.Valuation
