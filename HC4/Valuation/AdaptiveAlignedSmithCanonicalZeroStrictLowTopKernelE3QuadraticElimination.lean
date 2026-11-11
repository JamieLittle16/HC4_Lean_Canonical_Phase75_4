import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3FinalResolution
import HC4.Valuation.QuadraticTransverseCapSourceFullClosure
import Mathlib.Tactic

/-!
# Elimination of the reachable pure-longitudinal quadratic E3 relevel

The E3 packet supplies an honest represented determinant-one source,
an actual exact marked-gradient collision, and the transverse
quadratic cap when the first-contact order gap equals two.

The source-level quadratic-cap collision theorem now excludes *all*
transverse determinant ranks, so the entire gap-two pure E3 branch
is impossible.  No final-resolution extractor is required.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- **The gap-two pure E3 configuration is impossible.**
The source cap, determinant-one and exact marked collision all
come from the original represented source, with no new assumptions. -/
theorem PureLongitudinalMarkedE3Data.quadratic_relevel_impossible
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (hr :
      T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder = 2) :
    False := by
  have hbound :
      HasReverseWeightBound topKernelMarkedAxisNatWeight 2
        T.topKernelReesSource := by
    simpa [hr] using
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        D.coefficient_ne_zero D.topFace_eq
  have hzero :
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) =
        (fun _ : Fin 4 => (0 : K)) := by
    funext i
    fin_cases i <;> rfl
  have hright :
      (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    funext i
    refine Fin.cases ?_ (fun k : Fin 3 => ?_) i
    · simp [coordinateAxisPoint, Fin.cons]
    · simp [coordinateAxisPoint, Fin.cons]
  have hcoll :
      HasExactGradientCollision T.topKernelReesSource
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    rw [hzero, hright]
    exact T.topKernelReesSource_exactCollision
  exact quadraticTransverseCap_two_source_markedCollision_impossible
    T.topKernelReesSource hbound
    T.topKernelReesSource_hessianDeterminant_eq_one hcoll

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
