import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarCarrier
import Mathlib.Tactic

/-!
# Exact ratio equation on the A19 planar source carrier

The second retained affine equation of `QsOtherFacetPlanarCarrierPackage` was
constructed from a maximal ratio wall.  This file exposes the invariant form
of that equation between any two *actual source* support exponents.  It is the
source-honest support-plane identity used by the quotient-fiber reconstruction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

private theorem finsupp_weight_sub_scaled_fin4
    (a b : ℤ) (w v : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun i => a * w i - b * v i) e =
      a * Finsupp.weight w e - b * Finsupp.weight v e := by
  have h := HC4.Newton.finsupp_weight_fin4_linear_combination
    a w (fun i => (-b) * v i) e
  have hscaled := HC4.Newton.finsupp_weight_fin4_linear_combination
    (-b) v (fun _ => 0) e
  have hzero : Finsupp.weight (fun _ : Fin 4 => (0 : ℤ)) e = 0 := by
    simp [Finsupp.weight_apply]
  rw [hzero] at hscaled
  simp only [add_zero] at hscaled
  rw [h, hscaled]
  ring

/-- Every support point satisfies the unscaled maximal-ratio wall equation. -/
theorem QsOtherFacetPlanarCarrierPackage.support_wall_gap_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    P.pairGap *
        (Finsupp.weight (qsOtherFacetSkewWeight C next) e -
          qsOtherFacetSkewLevel C next) =
      P.skewGap * (qsOtherFacetPairDegree next e - 1) := by
  have hw := P.support_wall_level he
  rw [P.wallWeight_eq, P.wallLevel_eq] at hw
  rw [finsupp_weight_sub_scaled_fin4] at hw
  rw [finsupp_weight_qsOtherFacetPairWeight] at hw
  linarith

/-- **Source-honest wall ratio.**  For any two actual support exponents, the
pair-degree gap from the locked ray and the neutral-skew gap have the same
ratio.  This removes the construction-specific `pairGap` and `skewGap` from
all downstream geometry. -/
theorem QsOtherFacetPlanarCarrierPackage.support_wall_ratio
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)
    {e h : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hh : h ∈ P.carrier.support) :
    (qsOtherFacetPairDegree next h - 1) *
        (Finsupp.weight (qsOtherFacetSkewWeight C next) e -
          qsOtherFacetSkewLevel C next) =
      (qsOtherFacetPairDegree next e - 1) *
        (Finsupp.weight (qsOtherFacetSkewWeight C next) h -
          qsOtherFacetSkewLevel C next) := by
  have heq := P.support_wall_gap_eq he
  have hhq := P.support_wall_gap_eq hh
  have hcross :
      P.pairGap *
          ((qsOtherFacetPairDegree next h - 1) *
            (Finsupp.weight (qsOtherFacetSkewWeight C next) e -
              qsOtherFacetSkewLevel C next)) =
        P.pairGap *
          ((qsOtherFacetPairDegree next e - 1) *
            (Finsupp.weight (qsOtherFacetSkewWeight C next) h -
              qsOtherFacetSkewLevel C next)) := by
    calc
      P.pairGap *
          ((qsOtherFacetPairDegree next h - 1) *
            (Finsupp.weight (qsOtherFacetSkewWeight C next) e -
              qsOtherFacetSkewLevel C next)) =
        (qsOtherFacetPairDegree next h - 1) *
          (P.pairGap *
            (Finsupp.weight (qsOtherFacetSkewWeight C next) e -
              qsOtherFacetSkewLevel C next)) := by ring
      _ = (qsOtherFacetPairDegree next h - 1) *
          (P.skewGap * (qsOtherFacetPairDegree next e - 1)) := by rw [heq]
      _ = (qsOtherFacetPairDegree next e - 1) *
          (P.skewGap * (qsOtherFacetPairDegree next h - 1)) := by ring
      _ = (qsOtherFacetPairDegree next e - 1) *
          (P.pairGap *
            (Finsupp.weight (qsOtherFacetSkewWeight C next) h -
              qsOtherFacetSkewLevel C next)) := by rw [hhq]
      _ = P.pairGap *
          ((qsOtherFacetPairDegree next e - 1) *
            (Finsupp.weight (qsOtherFacetSkewWeight C next) h -
              qsOtherFacetSkewLevel C next)) := by ring
  exact mul_left_cancel₀ (ne_of_gt P.pairGap_pos) hcross

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
