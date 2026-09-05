import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactWeightedSchurShear
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySourceSchurClock
import Mathlib.Tactic

/-!
# A19.R18: transport the straightened Euler-Schur block to the binary family

A19.123 obtains the binary-homogenized family by inflating the three transverse
source coordinates once.  Ordinary Hessian entries acquire chain-rule factors
under that substitution, but the Euler-scaled Hessian acquires exactly the
matching source-coordinate factors.  Hence Euler-scaled Hessian formation
commutes *literally* with the three transverse inflations.

This is the representation bridge needed by the final R18 coefficient
calculation.  It transports the already-green weighted-Euler Schur
straightening from the honest contact Rees to the binary-homogenized family,
where A19.136/R20 supplies the exact parameter clock.  No new geometry,
homogeneity hypothesis, localization, or division is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The simultaneous unit transverse inflation as one ring homomorphism. -/
noncomputable def unitTransverseInflateRingHom :
    MvPolynomial (Fin 4) (Polynomial K) →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
  (kernelInflateHom (K := K) (3 : Fin 4) 1).comp
    ((kernelInflateHom (K := K) (2 : Fin 4) 1).comp
      (kernelInflateHom (K := K) (1 : Fin 4) 1))

@[simp]
theorem unitTransverseInflateRingHom_apply
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    unitTransverseInflateRingHom (K := K) F =
      unitTransverseInflateFamily (K := K) F := by
  rfl

/-- Euler scaling cancels exactly the source-coordinate chain-rule factors of
simultaneous unit transverse inflation. -/
theorem eulerScaledHessian_unitTransverseInflateFamily
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.eulerScaledHessian
        (unitTransverseInflateFamily (K := K) F) i j =
      unitTransverseInflateFamily (K := K)
        (HC4.Polynomial.eulerScaledHessian F i j) := by
  ext d
  rw [coeff_eulerScaledHessian, coeff_unitTransverseInflateFamily,
    coeff_unitTransverseInflateFamily, coeff_eulerScaledHessian]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Euler-scaled Hessian four-block of the actual binary-homogenized family. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryEulerHessianFourBlock
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((HC4.Polynomial.eulerScaledHessian P.binaryHomogenizedFamily).submatrix rho rho)

/-- The binary Euler block is exactly the contact Euler block transported by
the simultaneous transverse-inflation ring homomorphism. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryEulerHessianFourBlock_eq_map_contact
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    P.binaryEulerHessianFourBlock rho =
      (P.contactEulerHessianFourBlock rho).map
        (unitTransverseInflateRingHom (K := K)) := by
  apply GeneralFourBlock.ext <;>
    simp [QsOtherFacetContactQuadraticReesPackage.binaryEulerHessianFourBlock,
      QsOtherFacetContactQuadraticReesPackage.contactEulerHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, GeneralFourBlock.map,
      QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily,
      eulerScaledHessian_unitTransverseInflateFamily]

/-- Perform the same weighted-Euler quotient straightening directly on the
binary Euler block. -/
noncomputable def QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  (P.binaryEulerHessianFourBlock rho).shearSecondComplement
    1 (P.profileWeight : MvPolynomial (Fin 4) (Polynomial K)) 1 1

/-- Straightening commutes with the transverse-inflation transport. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_eq_map_contact
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    P.binaryWeightedEulerShear rho =
      (P.contactWeightedEulerShear rho).map
        (unitTransverseInflateRingHom (K := K)) := by
  rw [QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear,
    P.binaryEulerHessianFourBlock_eq_map_contact]
  apply GeneralFourBlock.ext <;>
    simp only [QsOtherFacetContactQuadraticReesPackage.contactWeightedEulerShear,
      GeneralFourBlock.shearSecondComplement, GeneralFourBlock.map,
      map_add, map_mul, map_pow, map_natCast, map_ofNat, map_one,
      one_mul, mul_one, one_pow]

/-- The denominator-cleared straightened Schur determinant transports without
any denominator or loss of information. -/
@[simp]
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_schurDetCore
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    (P.binaryWeightedEulerShear rho).schurDetCore =
      unitTransverseInflateRingHom (K := K)
        (P.contactWeightedEulerShear rho).schurDetCore := by
  rw [P.binaryWeightedEulerShear_eq_map_contact]
  simp

/-- The active pivot transports through the same map. -/
@[simp]
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_activeDet
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    (P.binaryWeightedEulerShear rho).activeDet =
      unitTransverseInflateRingHom (K := K)
        (P.contactWeightedEulerShear rho).activeDet := by
  rw [P.binaryWeightedEulerShear_eq_map_contact]
  simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation