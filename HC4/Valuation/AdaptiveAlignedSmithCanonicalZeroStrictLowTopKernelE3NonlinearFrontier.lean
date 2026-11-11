import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3QuadraticElimination
import Mathlib.Tactic

/-!
# Pure-longitudinal E3: unconditional nonlinear lower-face frontier

The quadratic source marked-collision theorem has eliminated
transverse degree two at the first actual marked-axis contact.
Consequently the already-constructed pure lower-face frontier
can be sharpened from a three-constructor quadratic/rank-three/
kernel-opening trichotomy to an exact rank-three-facet or canonical
kernel-opening dichotomy.

No new final-resolution producer or ambient-state restart is used.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- The first nonzero marked-axis face in any reachable
pure-longitudinal E3 packet has transverse degree at least three.
The old lower bound two is strengthened by the now-closed
quadratic-source contradiction. -/
theorem PureLongitudinalMarkedE3Data.firstActualTransverseDegree_ge_three
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    3 ≤ T.topFace.degree -
      T.topKernelMarkedAxisFirstActualLayerOrder := by
  have htwo :
      2 ≤ T.topFace.degree -
        T.topKernelMarkedAxisFirstActualLayerOrder :=
    (P.pureLongitudinal_markedAxis_firstActual_transverseDegree_bounds
      D.coefficient_ne_zero D.topFace_eq).1
  have hne :
      T.topFace.degree -
        T.topKernelMarkedAxisFirstActualLayerOrder ≠ 2 := by
    intro hr
    exact D.quadratic_relevel_impossible P hr
  omega

/-- The entire pure E3 first-contact lower-face frontier is genuinely
nonlinear: either its exposed singular boundary vertex has rank three
on one coordinate facet, or its canonical codimension-two kernel
outcome is available.

The quadratic constructor is not merely ignored: it is eliminated
by the actual source marked-gradient collision theorem. -/
theorem PureLongitudinalMarkedE3Data.nonlinearRankThreeOrKernelOpening
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    (∃ (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
        (facet : HC4.Toric.ToricFacet),
        MvRankThreeOnFacet facet N.vertex.exponent) ∨
      (∃ (N : P.PureLongitudinalMarkedAxisLowerNonlinearData),
        Nonempty (CanonicalCodimensionTwoKernelOutcome
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder))) := by
  rcases P.pureLongitudinal_markedAxis_lowerBoundaryFrontier_nonempty
      D.coefficient_ne_zero D.topFace_eq with ⟨F⟩
  cases F with
  | quadratic hr =>
      exact (D.quadratic_relevel_impossible P hr).elim
  | rankThree N facet hthree =>
      exact Or.inl ⟨N, facet, hthree⟩
  | kernelOpening N outcome =>
      exact Or.inr ⟨N, ⟨outcome⟩⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
