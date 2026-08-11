import HC4.Valuation.ActualParameterLayer
import HC4.Valuation.BinarySmithOrderExtraction

/-!
# Exact first post-transform face of strict symmetric Smith improvement

Strict symmetric Smith improvement proves that the conformally transformed
family has a common parameter factor.  Removing that one factor does not,
by itself, prove that the resulting special fibre is nonzero: the incoming
coefficients may have had more parameter order than the binary lower bound.

This file records the exact statement available without an additional
attainment hypothesis.  The new special fibre is precisely the *first
parameter coefficient layer* of the pre-extraction Smith family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Removing one common parameter factor converts the parameter-one layer
of the original family exactly into the special fibre of the quotient. -/
theorem polynomialFamilySpecialFiber_commonParameterFactor_one_eq_layer_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv : HasCommonParameterFactor 1 P) :
    polynomialFamilySpecialFiber
      (commonParameterFactorFamily 1 P hdiv) =
      familyParameterLayer P 1 := by
  ext d
  rw [familyParameterLayer_coeff]
  unfold polynomialFamilySpecialFiber
  rw [MvPolynomial.coeff_map]
  have hfactor :=
    commonParameterFactorFamily_coeff_factorisation 1 P hdiv d
  have hcoeff_one := congrArg (fun c : Polynomial K => c.coeff 1) hfactor
  simpa using hcoeff_one.symm

/-- The strict symmetric Smith branch has an exact post-transform face:
it is the parameter-one coefficient potential of the integral Smith family.
This is the strongest conclusion available from strict improvement and the
binary coefficient-order lower bound alone. -/
theorem strictSymmetricImprovement_postSpecialFiber_eq_layer_one
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HC4.Newton.HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P) 0
        (fun e => (base e : ℤ))) :
    let Pram := parameterRamificationFamily (K := K) 10 P
    let hsmith := strictSymmetricImprovement_integralSmithDivisibility
      (K := K) base P hbase hstrict
    let Psmith := integralSmithConformalFamily 2 2 Pram hsmith
    let hcommon := strictSymmetricImprovement_commonParameterFactor
      (K := K) base P hbase hstrict hsmith
    polynomialFamilySpecialFiber
      (commonParameterFactorFamily 1 Psmith hcommon) =
      familyParameterLayer Psmith 1 := by
  dsimp
  exact polynomialFamilySpecialFiber_commonParameterFactor_one_eq_layer_one
    (K := K) _ _

/-- Strict improvement alone supplies no attainment statement for the
parameter-one layer.  Thus callers which need a nonzero post-transform
special fibre must additionally provide a first-level attainment certificate
or extract the maximal common parameter factor. -/
def HasStrictSmithFirstLayerAttainment
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  familyParameterLayer P 1 ≠ 0

end

end HC4.Valuation
