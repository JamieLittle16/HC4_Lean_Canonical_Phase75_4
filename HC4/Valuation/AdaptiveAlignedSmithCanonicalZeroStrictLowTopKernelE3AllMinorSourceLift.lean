import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3SourceMinorLift
import HC4.Valuation.WeightedHessianMinorInitial
import Mathlib.Tactic

/-!
# Source-honest lifting of arbitrary Hessian two-by-two minors in nonlinear E3

The weighted-initial-form calculus already proves that a nonzero
arbitrary (including non-principal) two-by-two Hessian minor on a
maximal-weight face forces the corresponding minor on the original
polynomial to be nonzero.

The pure-longitudinal E3 first actual face is exactly the maximal
transverse-weight face of the *unchanged* represented source at the
reduced cap D-j.  Thus the weighted theorem applies directly.

At a further coordinate-max kernel opening the same algebra lifts a
minor from the child to its immediate parent.  A child-to-original-source
lift requires provenance of the entire canonical opening chain; mere
support containment is not enough and is not assumed here.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- An arbitrary nonzero 2x2 Hessian minor on the child of a
coordinate-max opening already occurs on the parent.  No source
provenance beyond the exact single opening is used. -/
theorem canonicalCoordinateMaxOpening_parentMinor_of_childMinor
    {F : MvPolynomial (Fin 4) K}
    (O : CanonicalCoordinateMaxKernelOpeningData F)
    (i j k l : Fin 4)
    (hminor : hessianTwoByTwoMinor O.child i j k l ≠ 0) :
    hessianTwoByTwoMinor O.parent i j k l ≠ 0 := by
  apply hessianTwoByTwoMinor_ne_zero_of_initialForm_ne_zero
    O.weight_bound i j k l
  rw [O.child_eq_initialForm] at hminor
  exact hminor

/-- A rank-two Hessian witness on an opened child forces a genuinely
nonzero two-by-two Hessian minor on its immediate parent. -/
theorem canonicalCoordinateMaxOpening_parentRankTwo_of_childRankTwo
    {F : MvPolynomial (Fin 4) K}
    (O : CanonicalCoordinateMaxKernelOpeningData F)
    (htwo : O.ChildHessianRankTwoWitness) :
    ∃ i j k l : Fin 4,
      hessianTwoByTwoMinor O.parent i j k l ≠ 0 := by
  rcases htwo with ⟨i, j, k, l, hminor⟩
  have hminorChild : hessianTwoByTwoMinor O.child i j k l ≠ 0 :=
    hminor
  exact ⟨i, j, k, l,
    canonicalCoordinateMaxOpening_parentMinor_of_childMinor
      O i j k l hminorChild⟩

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- **All-minor analogue of the green principal-minor source lift.**

A nonzero arbitrary Hessian 2x2 minor on the *first actual* marked-axis
face lifts to the same polynomial minor on the original represented
determinant-one source.  The reason is an exact maximal transverse
initial-form identity, not a false layerwise noncancellation claim. -/
theorem PureLongitudinalMarkedE3Data.firstActualTwoByTwoMinor_sourceLift
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (i j k l : Fin 4)
    (hminor :
      hessianTwoByTwoMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j k l ≠ 0) :
    hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0 := by
  have hbound :
      HC4.Polynomial.IsWeightLE
        (fun i => (topKernelMarkedAxisNatWeight i : ℤ))
        ((T.topFace.degree -
          T.topKernelMarkedAxisFirstActualLayerOrder : ℕ) : ℤ)
        T.topKernelReesSource := by
    intro d hd
    have hnat :=
      P.pureLongitudinal_markedAxis_firstActual_sourceWeightBound
        D.coefficient_ne_zero D.topFace_eq d hd
    rw [weight_topKernelMarkedAxisIntWeight]
    rw [weight_topKernelMarkedAxisNatWeight] at hnat
    exact_mod_cast hnat
  rw [P.pureLongitudinal_markedAxis_firstActualLayer_eq_initialForm
    D.coefficient_ne_zero D.topFace_eq] at hminor
  exact hessianTwoByTwoMinor_ne_zero_of_initialForm_ne_zero
    hbound i j k l hminor

/-- Rank-two Hessian geometry actually on the first actual face
therefore gives a nonzero arbitrary Hessian 2x2 minor on the
unchanged represented source. -/
theorem PureLongitudinalMarkedE3Data.firstActualRankTwo_sourceRankTwo
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data)
    (htwo :
      ∃ i j k l : Fin 4,
        HC4.Polynomial.hessian
          (familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder) i j *
          HC4.Polynomial.hessian
            (familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
              T.topKernelMarkedAxisFirstActualLayerOrder) k l -
          HC4.Polynomial.hessian
            (familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
              T.topKernelMarkedAxisFirstActualLayerOrder) i l *
          HC4.Polynomial.hessian
            (familyParameterLayer T.topKernelMarkedAxisFirstContactFamily
              T.topKernelMarkedAxisFirstActualLayerOrder) k j ≠ 0) :
    ∃ i j k l : Fin 4,
      hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0 := by
  rcases htwo with ⟨i, j, k, l, hminor⟩
  have hminorFace :
      hessianTwoByTwoMinor
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder) i j k l ≠ 0 :=
    hminor
  exact ⟨i, j, k, l,
    D.firstActualTwoByTwoMinor_sourceLift P i j k l hminorFace⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
