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

/-- The Schur block construction itself is family-theoretic; keeping this
generic prevents the large HC4 frontier package from entering coefficient
normalization. -/
noncomputable def centralDeficitSchurBlockOf
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((parameterFirstHessian Q).submatrix
      centralDeficitSchurPerm centralDeficitSchurPerm)

/-- Constant coefficient of the active determinant for an arbitrary family. -/
omit [IsAlgClosed K] in
theorem centralDeficitSchurBlockOf_activeDet_coeff_zero_eq
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).activeDet.coeff 0 =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer Q 0)
        (0 : Fin 4) (3 : Fin 4) := by
  have hsym :
      HC4.Polynomial.hessian (familyParameterLayer Q 0)
          (0 : Fin 4) (3 : Fin 4) =
        HC4.Polynomial.hessian (familyParameterLayer Q 0)
          (3 : Fin 4) (0 : Fin 4) := by
    change
      MvPolynomial.pderiv 3
          (MvPolynomial.pderiv 0 (familyParameterLayer Q 0)) =
        MvPolynomial.pderiv 0
          (MvPolynomial.pderiv 3 (familyParameterLayer Q 0))
    exact pderiv_comm_commRing (3 : Fin 4) (0 : Fin 4)
      (familyParameterLayer Q 0)
  unfold centralDeficitSchurBlockOf GeneralFourBlock.activeDet
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply,
    centralDeficitSchurPerm_zero, centralDeficitSchurPerm_one]
  change
    Polynomial.constantCoeff
      (parameterFirstHessian Q (0 : Fin 4) 0 *
          parameterFirstHessian Q (3 : Fin 4) 3 -
        parameterFirstHessian Q (0 : Fin 4) 3 *
          parameterFirstHessian Q (0 : Fin 4) 3) =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer Q 0) (0 : Fin 4) (3 : Fin 4)
  rw [map_sub, map_mul, map_mul]
  simp only [Polynomial.constantCoeff_apply]
  rw [parameterFirstHessian_coeff Q 0 (0 : Fin 4) 0,
    parameterFirstHessian_coeff Q 0 (3 : Fin 4) 3,
    parameterFirstHessian_coeff Q 0 (0 : Fin 4) 3]
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [hsym]

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
  centralDeficitSchurBlockOf P.centralDeficitFamily

/-- Displaying the Schur four-block recovers the literal permuted complete
source Hessian. -/
theorem centralDeficitSchurBlock_matrix :
    (centralDeficitSchurBlock (P := P)).matrix =
      (parameterFirstHessian P.centralDeficitFamily).submatrix
        centralDeficitSchurPerm centralDeficitSchurPerm := by
  unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact parameterFirstHessian_symmetric
    P.centralDeficitFamily
    (centralDeficitSchurPerm i) (centralDeficitSchurPerm j)

/-- Constant coefficient of the active determinant is the honest Hessian
principal minor of total-deficit layer zero in coordinates `(0,3)`. -/
theorem centralDeficitSchurBlock_activeDet_coeff_zero_eq :
    (centralDeficitSchurBlock (P := P)).activeDet.coeff 0 =
      HC4.Polynomial.hessianPrincipalMinor
        (familyParameterLayer P.centralDeficitFamily 0)
        (0 : Fin 4) (3 : Fin 4) := by
  exact centralDeficitSchurBlockOf_activeDet_coeff_zero_eq
    P.centralDeficitFamily

/-- The active determinant has a genuinely nonzero constant coefficient. -/
theorem centralDeficitSchurBlock_activeDet_coeff_zero_ne
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (centralDeficitSchurBlock (P := P)).activeDet.coeff 0 ≠ 0 := by
  rw [centralDeficitSchurBlock_activeDet_coeff_zero_eq (P := P)]
  rw [G.centralDeficitFamily_layer_zero_eq hthree houtThree]
  rw [← G.exposure_face_eq]
  exact G.exposure_rankTwo_minor

/-- The reordered block is still the complete Hessian of the honest singular
total-deficit family. -/
theorem centralDeficitSchurBlock_determinantCore_eq_zero :
    (centralDeficitSchurBlock (P := P)).determinantCore = 0 := by
  calc
    (centralDeficitSchurBlock (P := P)).determinantCore =
        (centralDeficitSchurBlock (P := P)).matrix.det :=
      (GeneralFourBlock.matrix_det (centralDeficitSchurBlock (P := P))).symm
    _ =
        ((parameterFirstHessian P.centralDeficitFamily).submatrix
          centralDeficitSchurPerm centralDeficitSchurPerm).det := by
      rw [centralDeficitSchurBlock_matrix (P := P)]
    _ = (parameterFirstHessian P.centralDeficitFamily).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = 0 := by
      rw [parameterFirstHessian_det, P.centralDeficitFamily_hessian_zero]
      simp

/-- The whole denominator-cleared binary Schur determinant vanishes,
not merely its first few coefficients. -/
theorem centralDeficitSchurBlock_schurDetCore_eq_zero :
    (centralDeficitSchurBlock (P := P)).schurDetCore = 0 :=
  GeneralFourBlock.schurDetCore_eq_zero_of_determinantCore_eq_zero
    (centralDeficitSchurBlock (P := P))
    (centralDeficitSchurBlock_determinantCore_eq_zero (P := P))

/-- Series-facing form: all reflected coefficient relations are contained in
one exact polynomial identity. -/
theorem centralDeficitSchurSeries_determinant_eq_zero :
    (centralDeficitSchurBlock (P := P)).polynomialSchurSeries.determinant = 0 := by
  rw [GeneralFourBlock.polynomialSchurSeries_determinant]
  rw [centralDeficitSchurBlock_determinantCore_eq_zero (P := P)]
  simp

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
