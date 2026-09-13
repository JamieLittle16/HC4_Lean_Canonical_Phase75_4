import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelOpeningSecondZeroSchurClock
import Mathlib.Tactic

/-!
# A18.4.98: complete finite filtered rank-three closure of a kernel opening

A18.4.96 closes the first scalar-Schur tail unless that tail is genuinely rank
one.  A18.4.97 converts precisely that residual branch to the repository's
exact binary zero-Schur clock.

This file consumes the binary clock geometrically rather than through its
historical repair-state wrapper.

* residual binary defect zero gives an actual nondegenerate first binary tail;
* positive residual gives a nonzero determinant-zero binary tail and hence a
  rank-one pivot;
* the associated exact rank-one Schur clock has a first transverse layer;
  preterminally its kernel coefficient is zero and its off-diagonal
  coefficient is nonzero, while at closing an explicit transverse coefficient
  is nonzero.

Together with the two retained scalar pivots, every branch therefore supplies
a third independent filtered Hessian direction.  The rank ladder is finite:
there is no recursive repair call and no rational-scale descent in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Concrete binary departure at the final stage of the filtered rank ladder. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningBinaryDeparture
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K)) : Type (u + 1)
  | nondegenerate
      (residual_zero : E.residualDefect = 0)
      (det_ne_zero :
        E.tailSeries.active.coeff 0 * E.tailSeries.kernel.coeff 0 -
          E.tailSeries.offDiag.coeff 0 * E.tailSeries.offDiag.coeff 0 ≠ 0)
  | preterminalLeft
      (residual_pos : 0 < E.residualDefect)
      (pivot : E.tailSeries.LeftPivot)
      (clock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (clock_eq : clock = E.toRankOneClockLeft residual_pos pivot)
      (first_lt : clock.firstOrder < clock.defect)
      (kernel_zero : clock.series.kernel.coeff clock.firstOrder = 0)
      (offDiag_ne_zero : clock.series.offDiag.coeff clock.firstOrder ≠ 0)
  | preterminalRight
      (residual_pos : 0 < E.residualDefect)
      (pivot : E.tailSeries.RightAxisPivot)
      (clock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (clock_eq : clock = E.toRankOneClockRight residual_pos pivot)
      (first_lt : clock.firstOrder < clock.defect)
      (kernel_zero : clock.series.kernel.coeff clock.firstOrder = 0)
      (offDiag_ne_zero : clock.series.offDiag.coeff clock.firstOrder ≠ 0)
  | closingLeft
      (residual_pos : 0 < E.residualDefect)
      (pivot : E.tailSeries.LeftPivot)
      (clock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (clock_eq : clock = E.toRankOneClockLeft residual_pos pivot)
      (first_eq : clock.firstOrder = clock.defect)
      (transverse :
        clock.series.offDiag.coeff clock.defect ≠ 0 ∨
          clock.series.kernel.coeff clock.defect ≠ 0)
  | closingRight
      (residual_pos : 0 < E.residualDefect)
      (pivot : E.tailSeries.RightAxisPivot)
      (clock : ExactRankOneSchurClockAt (MvPolynomial (Fin 4) K))
      (clock_eq : clock = E.toRankOneClockRight residual_pos pivot)
      (first_eq : clock.firstOrder = clock.defect)
      (transverse :
        clock.series.offDiag.coeff clock.defect ≠ 0 ∨
          clock.series.kernel.coeff clock.defect ≠ 0)

/-- The binary exact clock is exhausted by concrete coefficient geometry. -/
noncomputable def kernelOpeningBinaryDeparture
    (E : ExactZeroSchurClock (MvPolynomial (Fin 4) K)) :
    AdaptiveAlignedSmithCanonicalKernelOpeningBinaryDeparture E := by
  refine Classical.choice ?_
  by_cases hres0 : E.residualDefect = 0
  · exact ⟨.nondegenerate hres0
      (E.tail_constant_det_ne_zero_of_residual_zero hres0)⟩
  · have hres : 0 < E.residualDefect := Nat.pos_of_ne_zero hres0
    rcases E.tail_pivot_of_residual_pos hres with hleft | hright
    · let S := E.toRankOneClockLeft hres hleft
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · exact ⟨.preterminalLeft hres hleft S rfl hpre
          (S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre)
          (S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre)⟩
      · have htrans := S.series.transverse_nonzero_at_first S.hasTransverse
        have hfirst :
            S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
          simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
        rw [hfirst] at htrans
        exact ⟨.closingLeft hres hleft S rfl hclose htrans⟩
    · let S := E.toRankOneClockRight hres hright
      rcases lt_or_eq_of_le S.firstOrder_le_defect with hpre | hclose
      · exact ⟨.preterminalRight hres hright S rfl hpre
          (S.kernel_coeff_firstOrder_eq_zero_of_preterminal hpre)
          (S.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre)⟩
      · have htrans := S.series.transverse_nonzero_at_first S.hasTransverse
        have hfirst :
            S.series.firstPositiveTransverseOrder S.hasTransverse = S.defect := by
          simpa [ExactRankOneSchurClockAt.firstOrder] using hclose
        rw [hfirst] at htrans
        exact ⟨.closingRight hres hright S rfl hclose htrans⟩

/-- Complete filtered rank-three geometry for the genuine rank-one opening.
The first constructor is the already-closed first-tail event; the second
retains both scalar pivots and the exact final binary departure. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningCompleteFilteredRankThreeGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) : Type (u + 1)
  | firstTail
      (geometry : AdaptiveAlignedSmithCanonicalKernelOpeningFilteredRankThreeGeometry G)
  | secondTail
      (pivot : AdaptiveAlignedSmithCanonicalKernelOpeningSecondScalarPivot G)
      (zeroClock : AdaptiveAlignedSmithCanonicalKernelOpeningSecondZeroSchurClock pivot)
      (departure : AdaptiveAlignedSmithCanonicalKernelOpeningBinaryDeparture
        zeroClock.zeroClock)

/-- **Finite rank-ladder exhaustion of the rank-one kernel-opening branch.** -/
noncomputable def
    AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry.completeFilteredRankThreeGeometry
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (G : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source) :
    AdaptiveAlignedSmithCanonicalKernelOpeningCompleteFilteredRankThreeGeometry G := by
  refine Classical.choice ?_
  rcases G.threeTailFrontier with ⟨F⟩
  cases F with
  | rankThree geometry =>
      exact ⟨.firstTail geometry⟩
  | secondPivot pivot =>
      let Z := pivot.toZeroSchurClock
      exact ⟨.secondTail pivot Z (kernelOpeningBinaryDeparture Z.zeroClock)⟩

/-- Unified complete rank-three geometry for one zero-linear-jet saturated
kernel opening: either rank three is already visible on the post-opening
special fibre, or it appears at one of the two finite filtered Schur stages. -/
inductive AdaptiveAlignedSmithCanonicalKernelOpeningCompleteRankThreeGeometry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1)
  | actual
      (firstContact : AdaptiveAlignedSmithCanonicalCompleteKernelOpeningRankTwoGeometry source)
      (chart : AdaptiveAlignedSmithCanonicalExactActiveFourBlock firstContact.opening)
      (geometry : AdaptiveAlignedSmithCanonicalExactActiveRankThreeGeometry chart complexity)
  | filtered
      (rankOne : AdaptiveAlignedSmithCanonicalKernelOpeningRankOneGeometry source)
      (geometry : AdaptiveAlignedSmithCanonicalKernelOpeningCompleteFilteredRankThreeGeometry rankOne)

/-- **Sound complete saturated-kernel rank-three theorem.** -/
theorem ScaleAwareAdaptiveGeometricRestartState.kernelFreeOpening_completeRankThree_of_gradientAtZero
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel source.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber source.family).support,
        d kernel = 0)
    (hgrad :
      ∀ i : Fin 4,
        MvPolynomial.eval
            (fun _ : Fin 4 => (0 : Polynomial K))
            (MvPolynomial.pderiv i source.family) = 0) :
    Nonempty (AdaptiveAlignedSmithCanonicalKernelOpeningCompleteRankThreeGeometry
      source complexity) := by
  rcases source.kernelFreeOpening_rankThree_or_rankOne_of_gradientAtZero
      complexity kernel hkernel hactive hfree hgrad with ⟨F⟩
  cases F with
  | rankThree firstContact chart geometry =>
      exact ⟨.actual firstContact chart geometry⟩
  | rankOne geometry =>
      exact ⟨.filtered geometry geometry.completeFilteredRankThreeGeometry⟩

end

end HC4.Valuation