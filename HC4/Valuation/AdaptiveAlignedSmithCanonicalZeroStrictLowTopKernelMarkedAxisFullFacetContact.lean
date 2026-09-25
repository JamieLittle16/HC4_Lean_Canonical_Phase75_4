import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFullFacetRefinement
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayTerminal
import Mathlib.Tactic

/-!
# E2: the full marked-facet branch has a genuine lower first contact

If the singular maximal ordinary top face is completely supported on the
marked `.qs` facet, strict-low source provenance prevents the represented
determinant-one source from being confined there: A19.87 supplies a nonlinear
source monomial with coordinate-zero exponent at least two.

Thus the existing strengthened `.qs` first-nonfacet selector applies
directly, with no rank-three hypothesis on the top-face exposed vertex.  The
result is the honest lower first-contact cross-facet carrier already used by
the green A19 chain.

Its balance-free affine ray then has the standard finite endpoint split:
rank three on `.qs` (where the mature affine terminal argument forces
coefficient degree one), or a genuine codimension-two boundary exponent.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Full confinement of the maximal top face to `.qs` still leaves honest
nonlinear represented-source support outside `.qs`, by strict-low source
provenance. -/
theorem nonlinearOutsideMarkedFacet_of_topFaceOnMarkedFacet
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    HC4.Newton.HasNonlinearOutsideFacet .qs
      (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family) := by
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨d, hd, hdeg, hd0, _hcodim⟩
  refine ⟨d, hd, hdeg, ?_⟩
  intro hon
  have hz : d (0 : Fin 4) = 0 := by
    have htoric :=
      (HC4.Polynomial.onFacet_toToricExponent_iff .qs d).1 hon
    simpa [HC4.Polynomial.facetOmittedCoordinate] using htoric
  omega

/-- Canonical honest lower first-contact carrier forced by the full marked
facet. -/
noncomputable def fullMarkedFacetFirstNonfacetCrossFacetData
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      (K := K) T .qs := by
  have htop :
      HC4.Newton.TopDegreeOnFacet .qs T.topFace.degree
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) :=
    T.topFaceOnFacet_topDegreeOnFacet .qs hfacet
  have hout :
      HC4.Newton.HasNonlinearOutsideFacet .qs
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) :=
    P.nonlinearOutsideMarkedFacet_of_topFaceOnMarkedFacet hfacet
  exact T.firstNonfacetCrossFacetData_qs htop hout

/-- Finite A19 endpoint retained by the full marked-facet branch. -/
inductive TopKernelMarkedAxisFullFacetContactFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    Type (u + 1)
  | rankThree
      (rankThree :
        HC4.Newton.MvRankThreeOnFacet .qs
          (P.fullMarkedFacetFirstNonfacetCrossFacetData hfacet).ray.facetExponent)
      (degree_one :
        (P.fullMarkedFacetFirstNonfacetCrossFacetData hfacet)
          .ray.zeroCoefficientPolynomial.natDegree = 1)
  | codimensionTwo
      (boundary :
        HC4.Newton.MvExponentOnCodimensionTwoBoundary
          (P.fullMarkedFacetFirstNonfacetCrossFacetData hfacet).ray.facetExponent)

/-- **Full marked-facet E2 endpoint split.**

The passive confinement case is replaced by an actual lower first-contact
carrier and then by the already-green affine rank-three/codimension-two split.
-/
theorem fullMarkedFacetContactFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (hfacet : HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face) :
    Nonempty (P.TopKernelMarkedAxisFullFacetContactFrontier hfacet) := by
  let C := P.fullMarkedFacetFirstNonfacetCrossFacetData hfacet
  rcases C.ray.zero_terminalCertificate_or_codimensionTwo C.hessian_zero with
    hterminal | htwo
  · have hthree :
        HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent :=
      hterminal.1
    have hdegree : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
      C.qs_ray_terminal_degreeOne hthree
    exact ⟨.rankThree (by simpa [C] using hthree) (by simpa [C] using hdegree)⟩
  · exact ⟨.codimensionTwo (by simpa [C] using htwo)⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
