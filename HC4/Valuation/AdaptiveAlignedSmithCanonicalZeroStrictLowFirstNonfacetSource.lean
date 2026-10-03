import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeFacetSplit
import HC4.Newton.FirstNonfacetContact
import Mathlib.Tactic

/-!
# A19.59: source hypotheses for the zero strict-low first-nonfacet splice

A19.58 reduces the rank-three boundary branch to either an already constructed
cross-facet exact face or confinement of the singular maximal ordinary top
face to one coordinate facet.  In the confined branch, the generic
`FirstNonfacetContact` theorem wants source-level hypotheses on the represented
special fibre.

This file exports the three hypotheses that are already forced by the retained
zero-defect carrier:

* the selected maximal degree bounds every nonlinear source monomial;
* the represented special fibre is polynomial Monge--Ampere; and
* confinement of the selected maximal face is exactly `TopDegreeOnFacet` at
  that selected degree.

No outside-support witness or low-degree-tameness assertion is introduced
here; those are the remaining source-side inputs to the first-nonfacet
constructor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The selected top degree is a genuine nonlinear degree bound for the whole
represented special fibre. -/
theorem representedSpecialFiber_nonlinearDegreeBound_topFace
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HC4.Newton.NonlinearDegreeBound T.topFace.degree
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro d hd _hnonlinear
  exact T.topFace.maximal d hd

/-- Raw defect zero on the represented state is exactly the polynomial
Monge--Ampere equation on its special fibre. -/
theorem representedSpecialFiber_isPolynomialMongeAmpere
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    HC4.MongeAmpere.IsPolynomialMongeAmpere
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  unfold HC4.MongeAmpere.IsPolynomialMongeAmpere
  exact
    T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero

/-- If the actual singular maximal face is confined to a coordinate facet,
then every source monomial of the selected maximal degree lies on that facet.
This is the exact `TopDegreeOnFacet` input consumed by `FirstNonfacetContact`. -/
theorem topFaceOnFacet_topDegreeOnFacet
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hfacet : HC4.Polynomial.MvSupportOnFacet facet T.topFace.face) :
    HC4.Newton.TopDegreeOnFacet facet T.topFace.degree
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  intro d hd hdegree
  have hcoeff :
      MvPolynomial.coeff d
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hfaceMem : d ∈ T.topFace.face.support := by
    apply MvPolynomial.mem_support_iff.mpr
    rw [T.topFace.face_eq, HC4.Polynomial.coeff_initialForm]
    split
    · exact hcoeff
    · rename_i hweight
      exfalso
      apply hweight
      change
        Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d =
          (T.topFace.degree : ℤ)
      rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4]
      exact_mod_cast hdegree
  exact hfacet d hfaceMem

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
