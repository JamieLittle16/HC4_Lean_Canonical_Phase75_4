import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisEmptyRigidity
import Mathlib.Tactic

/-!
# E1 final form: marked-axis support frontier in the top-kernel linear-power case

The raw marked-axis support trichotomy has an `empty` constructor.  The
top-kernel linear-power rigidity theorem sharpens that constructor to a literal
nonzero pure longitudinal top power.

Thus the E-stage no longer has to reason about an opaque zero special fibre.
Its exact finite top-kernel support frontier is:

* a pure nonzero `X₀^D` singular top face, with transverse kernel coordinate;
* complete support of the top face on the marked `.qs` facet, with the
  marked-axis fibre carrying exactly the same support; or
* a genuine two-sided coordinate-zero cross-facet carrier on the actual
  singular top face.

This is classification only.  It introduces no terminal conclusion.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Final E1 support interface in the residual top-kernel linear-power branch. -/
inductive TopKernelMarkedAxisLinearPowerFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | pureLongitudinal
      (coefficient : K)
      (coefficient_ne_zero : coefficient ≠ 0)
      (topFace_eq :
        T.topFace.face =
          MvPolynomial.C coefficient *
            (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
      (kernel_ne_zero : kernelCoordinate ≠ (0 : Fin 4))
  | fullMarkedFacet
      (topFaceOnMarkedFacet :
        HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face)
      (support_eq :
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily).support =
            T.topFace.face.support)
  | crossFacet
      (data :
        CrossFacetInitialData T.topFace.face
          (crossFacetOppositeCoordinate (0 : Fin 4))
          (0 : Fin 4))

/-- **Completed E1 top-kernel marked-axis classification.** -/
theorem topKernelMarkedAxisLinearPowerFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelMarkedAxisLinearPowerFrontier := by
  cases T.topKernelMarkedAxisSupportFrontier with
  | empty hfibre =>
      rcases P.pureLongitudinalTopFace_of_markedAxisFibre_eq_zero hfibre with
        ⟨b, hb, hface, hk⟩
      exact ⟨.pureLongitudinal b hb hface hk⟩
  | full hfacet hsupp =>
      exact ⟨.fullMarkedFacet hfacet hsupp⟩
  | crossFacet data =>
      exact ⟨.crossFacet data⟩

/-- Canonical Type-valued E1 frontier used by the final-resolution adapter. -/
noncomputable def topKernelMarkedAxisLinearPowerFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.TopKernelMarkedAxisLinearPowerFrontier :=
  Classical.choice P.topKernelMarkedAxisLinearPowerFrontier_nonempty

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
