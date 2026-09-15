import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowResidualSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport
import HC4.Newton.FiniteSupportCrossFacetRayAffineRRTerminal
import Mathlib.Tactic

/-!
# A19.73: the `qs` zero strict-low rank-three branch reaches affine RR

A19.66 gives four possibilities below a rank-three singular top-face point.
For the marked `.qs` facet, the actual strict-low residual source witnesses
already rule out complete nonlinear source confinement: every one of the three
strict-low patterns produces a nonlinear source monomial with positive
coordinate `0`, whereas `.qs` is exactly the facet `d 0 = 0`.

In either remaining cross-facet branch, the omitted coordinate is literally
coordinate `0`, so A19.67 gives a contact-`0` balance-free ray.  A19.72 then
sends that exact ray either to the mature general affine RationalRigidity
terminal certificate or to a genuine codimension-two facet endpoint.

This module deliberately retains the ray and its endpoint stratum rather than
embedding the large RationalRigidity certificate a second time in the residual
type.  In the rank-three branch the complete certificate is recovered
canonically by `CrossFacetRayData.zero_rankThree_terminalCertificate`; keeping
the carrier light avoids expensive dependent-type normalization and preserves
all support, first-contact, and affine-slope provenance needed by later steps.
No torus balance, integral direction, or carrier transport is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.RationalRigidity
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19.73 `qs` residual reduction.**

A rank-three exposed boundary point on `.qs` leaves only:

* a retained top-face balance-free ray whose facet endpoint is either rank
  three on `.qs` or codimension two;
* a retained lower first-contact balance-free ray with the same endpoint
  split; or
* a literal source quadratic square in coordinate `0`.

In either rank-three ray branch, A19.72 immediately supplies the complete
affine RationalRigidity terminal certificate.  The complete nonlinear-
confinement branch is impossible directly from the strict-low source
witnesses. -/
theorem qs_rankThree_affineTerminal_or_codimensionTwo_or_quadraticSquare
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ R : HC4.Newton.CrossFacetRayData T.topFace.face (0 : Fin 4),
        HC4.Newton.MvRankThreeOnFacet .qs R.facetExponent ∨
          HC4.Newton.MvExponentOnCodimensionTwoBoundary R.facetExponent) ∨
      (∃ C :
          AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
            (K := K) T .qs,
        HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent ∨
          HC4.Newton.MvExponentOnCodimensionTwoBoundary C.ray.facetExponent) ∨
      (∃ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        HC4.Polynomial.ordinaryDegree4 d = 2 ∧
        d (0 : Fin 4) = 2 ∧
        ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0) := by
  rcases T.rankThree_crossFacet_or_firstNonfacetCrossFacet_or_quadraticSquare_or_nonlinearConfined
      .qs hthree with htop | hlower | hsquare | hconfined
  · rcases htop with ⟨D⟩
    have hfacet :
        (HC4.Newton.zeroCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty := by
      exact ⟨D.facetExponent,
        HC4.Newton.mem_zeroCoordinateSupport.mpr
          ⟨D.facet_mem, D.facet_coordinate_zero⟩⟩
    have hout :
        (HC4.Newton.positiveCoordinateSupport (0 : Fin 4) T.topFace.face).Nonempty := by
      exact ⟨D.outsideExponent,
        HC4.Newton.mem_positiveCoordinateSupport.mpr
          ⟨D.outside_mem, D.outside_coordinate_pos⟩⟩
    let R : HC4.Newton.CrossFacetRayData T.topFace.face (0 : Fin 4) :=
      HC4.Newton.crossFacetRayData hfacet hout
    rcases R.zero_terminalCertificate_or_codimensionTwo
        T.topFace_hessianDeterminant_eq_zero with hterminal | htwo
    · exact Or.inl ⟨R, Or.inl hterminal.1⟩
    · exact Or.inl ⟨R, Or.inr htwo⟩
  · rcases hlower with ⟨C⟩
    rcases C.ray.zero_terminalCertificate_or_codimensionTwo C.hessian_zero with
      hterminal | htwo
    · exact Or.inr (Or.inl ⟨C, Or.inl hterminal.1⟩)
    · exact Or.inr (Or.inl ⟨C, Or.inr htwo⟩)
  · simpa [HC4.Polynomial.facetOmittedCoordinate] using
      (Or.inr (Or.inr hsquare))
  · rcases T.terminal.pattern with hpure | hfirst | hsecond
    · rcases T.pureLongitudinal_sourceSupport hpure with
        ⟨d, hd, hdeg, hd0, _hd1, _hd2, _hd3⟩
      have hfacet := hconfined d hd hdeg
      have hz : d (0 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega
    · rcases T.lowNegativeFirst_sourceSupport hfirst with
        ⟨d, hd, hdeg, hd0, _hd2⟩
      have hfacet := hconfined d hd hdeg
      have hz : d (0 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega
    · rcases T.lowNegativeSecond_sourceSupport hsecond with
        ⟨d, hd, hdeg, hd0, _hd1⟩
      have hfacet := hconfined d hd hdeg
      have hz : d (0 : Fin 4) = 0 := by
        simpa [HC4.Toric.OnFacet] using hfacet
      omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
