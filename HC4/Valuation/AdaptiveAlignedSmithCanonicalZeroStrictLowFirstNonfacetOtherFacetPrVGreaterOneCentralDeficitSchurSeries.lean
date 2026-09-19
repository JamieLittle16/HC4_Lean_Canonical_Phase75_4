import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitReflectionDescent
import HC4.Newton.RankOneSchurSeriesAlignment
import Mathlib.Tactic

/-!
# Source-honest binary Schur series of the central total-deficit family

The central finite-staircase survivor carries an honest nonzero Hessian
principal minor in source coordinates `(0,3)`.  Reorder the complete
parameter-first Hessian of the total-deficit Rees family so that these two
coordinates form the active block.

This gives a denominator-cleared binary Schur polynomial series with:

* nonzero constant active determinant, coming from the actual central
  monomial;
* identically zero full determinant, because the complete total-deficit
  family is Hessian-singular;
* hence identically zero binary Schur determinant.

This packages all later reflected coefficient identities at once.  No
truncation, sparse subpolynomial, repair transition, or clock identification
is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Coordinate order `(0,3 | 2,1)`; the first two coordinates are exactly
the honest central rank-two principal block. -/
def centralDeficitSchurPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) 3

@[simp] theorem centralDeficitSchurPerm_zero :
    centralDeficitSchurPerm 0 = 0 := by decide

@[simp] theorem centralDeficitSchurPerm_one :
    centralDeficitSchurPerm 1 = 3 := by decide

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- Complete parameter-first Hessian of the total-deficit family, with the
central `(0,3)` principal block placed first. -/
noncomputable def centralDeficitSchurBlock :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((parameterFirstHessian P.centralDeficitFamily).submatrix
      centralDeficitSchurPerm centralDeficitSchurPerm)

/-- Displaying the Schur four-block recovers the literal permuted complete
source Hessian. -/
theorem centralDeficitSchurBlock_matrix :
    G.centralDeficitSchurBlock.matrix =
      (parameterFirstHessian P.centralDeficitFamily).submatrix
        centralDeficitSchurPerm centralDeficitSchurPerm := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact parameterFirstHessian_symmetric
    P.centralDeficitFamily
    (centralDeficitSchurPerm i) (centralDeficitSchurPerm j)

/-- Constant coefficient of the active determinant is the honest Hessian
principal minor of total-deficit layer zero in coordinates `(0,3)`. -/
theorem centralDeficitSchurBlock_activeDet_coeff_zero_eq :
    G.centralDeficitSchurBlock.activeDet.coeff 0 =
      hessianPrincipalMinor
        (familyParameterLayer P.centralDeficitFamily 0)
        (0 : Fin 4) (3 : Fin 4) := by
  have hsym :
      hessian (familyParameterLayer P.centralDeficitFamily 0)
          (0 : Fin 4) (3 : Fin 4) =
        hessian (familyParameterLayer P.centralDeficitFamily 0)
          (3 : Fin 4) (0 : Fin 4) := by
    change
      MvPolynomial.pderiv 3
          (MvPolynomial.pderiv 0
            (familyParameterLayer P.centralDeficitFamily 0)) =
        MvPolynomial.pderiv 0
          (MvPolynomial.pderiv 3
            (familyParameterLayer P.centralDeficitFamily 0))
    exact pderiv_comm_commRing (3 : Fin 4) (0 : Fin 4)
      (familyParameterLayer P.centralDeficitFamily 0)
  unfold centralDeficitSchurBlock GeneralFourBlock.activeDet
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply,
    centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  simp only [← Polynomial.coeff_zero_eq_eval_zero]
  simp_rw [parameterFirstHessian_coeff]
  unfold hessianPrincipalMinor
  rw [hsym]

/-- The active determinant has a genuinely nonzero constant coefficient. -/
theorem centralDeficitSchurBlock_activeDet_coeff_zero_ne
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.centralDeficitSchurBlock.activeDet.coeff 0 ≠ 0 := by
  rw [G.centralDeficitSchurBlock_activeDet_coeff_zero_eq]
  rw [G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  rw [← G.exposure_face_eq]
  exact G.exposure_rankTwo_minor

/-- The reordered block is still the complete Hessian of the honest singular
total-deficit family. -/
theorem centralDeficitSchurBlock_determinantCore_eq_zero :
    G.centralDeficitSchurBlock.determinantCore = 0 := by
  calc
    G.centralDeficitSchurBlock.determinantCore =
        G.centralDeficitSchurBlock.matrix.det :=
      (GeneralFourBlock.matrix_det G.centralDeficitSchurBlock).symm
    _ =
        ((parameterFirstHessian P.centralDeficitFamily).submatrix
          centralDeficitSchurPerm centralDeficitSchurPerm).det := by
      rw [G.centralDeficitSchurBlock_matrix]
    _ = (parameterFirstHessian P.centralDeficitFamily).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = 0 := by
      rw [parameterFirstHessian_det, P.centralDeficitFamily_hessian_zero]
      simp

/-- The whole denominator-cleared binary Schur determinant vanishes,
not merely its first few coefficients. -/
theorem centralDeficitSchurBlock_schurDetCore_eq_zero :
    G.centralDeficitSchurBlock.schurDetCore = 0 :=
  G.centralDeficitSchurBlock.schurDetCore_eq_zero_of_determinantCore_eq_zero
    G.centralDeficitSchurBlock_determinantCore_eq_zero

/-- Series-facing form: all reflected coefficient relations are contained in
one exact polynomial identity. -/
theorem centralDeficitSchurSeries_determinant_eq_zero :
    G.centralDeficitSchurBlock.polynomialSchurSeries.determinant = 0 := by
  rw [GeneralFourBlock.polynomialSchurSeries_determinant]
  rw [G.centralDeficitSchurBlock_determinantCore_eq_zero]
  simp

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
