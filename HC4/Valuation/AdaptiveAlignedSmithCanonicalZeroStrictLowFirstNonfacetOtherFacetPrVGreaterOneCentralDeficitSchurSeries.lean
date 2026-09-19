import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitReflectionDescent
import HC4.Valuation.PermutedFamilyHessianFourBlock
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
variable {K : Type u} [Field K] [CharZero K]

/-- Coordinate order `(0,3 | 2,1)`; the first two coordinates are exactly
the honest central rank-two principal block. -/
def centralDeficitSchurPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) 3

@[simp] theorem centralDeficitSchurPerm_zero :
    centralDeficitSchurPerm 0 = 0 := by decide

@[simp] theorem centralDeficitSchurPerm_one :
    centralDeficitSchurPerm 1 = 3 := by decide

@[simp] theorem centralDeficitSchurPerm_two :
    centralDeficitSchurPerm 2 = 2 := by decide

@[simp] theorem centralDeficitSchurPerm_three :
    centralDeficitSchurPerm 3 = 1 := by decide

/-- The Schur block construction itself is family-theoretic; keeping this
generic prevents the large HC4 frontier package from entering coefficient
normalization. -/
noncomputable def centralDeficitSchurBlockOf
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  permutedFamilyHessianFourBlock centralDeficitSchurPerm Q

/-- Constant coefficient of the first complementary column entries. -/
theorem centralDeficitSchurBlockOf_p_coeff_zero
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).p.coeff 0 =
      HC4.Polynomial.hessian (familyParameterLayer Q 0) 0 2 := by
  rw [centralDeficitSchurBlockOf, permutedFamilyHessianFourBlock_p]
  simp only [centralDeficitSchurPerm_zero, centralDeficitSchurPerm_two]
  exact parameterFirstHessian_coeff Q 0 (0 : Fin 4) 2

theorem centralDeficitSchurBlockOf_q_coeff_zero
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).q.coeff 0 =
      HC4.Polynomial.hessian (familyParameterLayer Q 0) 0 1 := by
  rw [centralDeficitSchurBlockOf, permutedFamilyHessianFourBlock_q]
  simp only [centralDeficitSchurPerm_zero, centralDeficitSchurPerm_three]
  exact parameterFirstHessian_coeff Q 0 (0 : Fin 4) 1

theorem centralDeficitSchurBlockOf_r_coeff_zero
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).r.coeff 0 =
      HC4.Polynomial.hessian (familyParameterLayer Q 0) 3 2 := by
  rw [centralDeficitSchurBlockOf, permutedFamilyHessianFourBlock_r]
  simp only [centralDeficitSchurPerm_one, centralDeficitSchurPerm_two]
  exact parameterFirstHessian_coeff Q 0 (3 : Fin 4) 2

theorem centralDeficitSchurBlockOf_s_coeff_zero
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).s.coeff 0 =
      HC4.Polynomial.hessian (familyParameterLayer Q 0) 3 1 := by
  rw [centralDeficitSchurBlockOf, permutedFamilyHessianFourBlock_s]
  simp only [centralDeficitSchurPerm_one, centralDeficitSchurPerm_three]
  exact parameterFirstHessian_coeff Q 0 (3 : Fin 4) 1

theorem centralDeficitSchurBlockOf_x_coeff_zero
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).x.coeff 0 =
      HC4.Polynomial.hessian (familyParameterLayer Q 0) 2 2 := by
  rw [centralDeficitSchurBlockOf, permutedFamilyHessianFourBlock_x]
  simp only [centralDeficitSchurPerm_two, centralDeficitSchurPerm_two]
  exact parameterFirstHessian_coeff Q 0 (2 : Fin 4) 2

theorem centralDeficitSchurBlockOf_y_coeff_zero
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).y.coeff 0 =
      HC4.Polynomial.hessian (familyParameterLayer Q 0) 2 1 := by
  rw [centralDeficitSchurBlockOf, permutedFamilyHessianFourBlock_y]
  simp only [centralDeficitSchurPerm_two, centralDeficitSchurPerm_three]
  exact parameterFirstHessian_coeff Q 0 (2 : Fin 4) 1

theorem centralDeficitSchurBlockOf_z_coeff_zero
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (centralDeficitSchurBlockOf Q).z.coeff 0 =
      HC4.Polynomial.hessian (familyParameterLayer Q 0) 1 1 := by
  rw [centralDeficitSchurBlockOf, permutedFamilyHessianFourBlock_z]
  simp only [centralDeficitSchurPerm_three, centralDeficitSchurPerm_three]
  exact parameterFirstHessian_coeff Q 0 (1 : Fin 4) 1

/-- Constant coefficient of the literal active `(0,3)` Hessian determinant
for an arbitrary parameter family.  This deliberately avoids mentioning the
four-block wrapper in the theorem statement, keeping kernel reduction small. -/
theorem centralDeficitActiveDet_coeff_zero_eq
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    (parameterFirstHessian Q (0 : Fin 4) 0 *
          parameterFirstHessian Q (3 : Fin 4) 3 -
        parameterFirstHessian Q (0 : Fin 4) 3 *
          parameterFirstHessian Q (0 : Fin 4) 3).coeff 0 =
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

variable [IsAlgClosed K]

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
noncomputable def centralDeficitSchurBlock
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  centralDeficitSchurBlockOf P.centralDeficitFamily

/-- The reordered block is still the complete Hessian of the honest singular
total-deficit family. -/
theorem centralDeficitSchurBlock_determinantCore_eq_zero :
    G.centralDeficitSchurBlock.determinantCore = 0 := by
  unfold centralDeficitSchurBlock centralDeficitSchurBlockOf
  rw [permutedFamilyHessianFourBlock_determinantCore_eq_det]
  rw [parameterFirstHessian_det, P.centralDeficitFamily_hessian_zero]
  simp

/-- The whole denominator-cleared binary Schur determinant vanishes,
not merely its first few coefficients. -/
theorem centralDeficitSchurBlock_schurDetCore_eq_zero :
    G.centralDeficitSchurBlock.schurDetCore = 0 :=
  GeneralFourBlock.schurDetCore_eq_zero_of_determinantCore_eq_zero
    G.centralDeficitSchurBlock
    (G.centralDeficitSchurBlock_determinantCore_eq_zero)

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
