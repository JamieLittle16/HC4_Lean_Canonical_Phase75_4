import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFullFacetContact
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetActualRankTwoClosure
import Mathlib.Tactic

/-!
# E2: reduced full marked-facet endpoint

The previous E2 step turns complete marked-facet confinement into the honest
lower `.qs` first-contact carrier.  The mature A19 lower-boundary chain then
does more than merely classify its rank-three branch:

* if the ray starts at codimension two, retain that literal boundary exponent;
* if the ray starts rank three on `.qs`, the far codimension-two alternative
  is impossible and the surviving different-facet endpoint already gives an
  actual rank-two Hessian chart on the represented determinant-one source.

Thus the full marked-facet branch has only these two assembly-facing outputs.
No repair tag or global progress conclusion is used.
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

/-- Final reduced geometry of the full marked-facet E2 branch. -/
inductive TopKernelMarkedAxisFullFacetReducedFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    Type (u + 1)
  | startCodimensionTwo
      (boundary :
        HC4.Newton.MvExponentOnCodimensionTwoBoundary
          (P.fullMarkedFacetRayFacetExponent hfacet))
  | actualRankTwo
      (geometry :
        AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented)

/-- **Reduced full marked-facet frontier.**

The existing A19 other-facet closure consumes every rank-three start into an
actual represented-source rank-two chart.  Only a genuinely codimension-two
starting endpoint remains geometric. -/
theorem fullMarkedFacetReducedFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    Nonempty (P.TopKernelMarkedAxisFullFacetReducedFrontier hfacet) := by
  let C := P.fullMarkedFacetFirstNonfacetCrossFacetData hfacet
  rcases C.ray.zero_terminalCertificate_or_codimensionTwo C.hessian_zero with
    hterminal | htwo
  · have hthree :
        HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent :=
      hterminal.1
    have houtcome :
        AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.QsLowerBoundaryOutcome C := by
      rcases C.qs_ray_outside_boundaryTransition hthree with
        houtThree | houtTwo
      · exact Or.inr (Or.inl houtThree)
      · exact Or.inr (Or.inr houtTwo)
    rcases C.qs_ray_boundaryOutcome_actualRankTwoHessianChart hthree houtcome with
      ⟨A⟩
    exact ⟨.actualRankTwo A⟩
  · exact ⟨.startCodimensionTwo (by
      simpa [C, fullMarkedFacetRayFacetExponent] using htwo)⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
