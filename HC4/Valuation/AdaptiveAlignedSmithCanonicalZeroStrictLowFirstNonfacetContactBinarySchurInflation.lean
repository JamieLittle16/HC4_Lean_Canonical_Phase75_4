import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryActiveInflation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryEulerSchurTransport
import Mathlib.Tactic

/-!
# A19.R18: full binary Schur transport through transverse inflation

The honest binary contact family is obtained from the contact Rees family by
simultaneously inflating source coordinates `1,2,3` by the parameter `tau`.
For the cyclic other-facet Schur order the active pair is transverse, the first
complementary direction is longitudinal `x₀`, and the second complementary
direction is the omitted transverse coordinate.  Hence the ordinary Hessian
four-block is obtained from the inflated contact block by the diagonal
congruence

    (tau, tau | 1, tau).

The generic `GeneralFourBlock.diagonalScale` covariance therefore gives the
exact factors

    schurA       : tau^4,
    schurB       : tau^5,
    schurC       : tau^6,
    schurDetCore : tau^10.

The existing R18 Euler-Schur transport already owns the simultaneous inflation
ring homomorphism; this module reuses that owner rather than introducing a
second copy.  All identities remain integral polynomial identities: no pivot
is inverted and no coefficientwise nonvanishing claim is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

-- CI anchor: elaborate the ordinary-Hessian Schur inflation transport.

/-- The common row/column chain-rule factor for simultaneous transverse
inflation. -/
def unitTransverseDerivativeCoefficient (i : Fin 4) : Polynomial K :=
  if i = 0 then 1 else Polynomial.X

/-- Entrywise ordinary-Hessian covariance for simultaneous transverse
inflation.  This is the non-Euler-scaled companion of the already-green
`eulerScaledHessian_unitTransverseInflateFamily`. -/
theorem hessian_unitTransverseInflateFamily_entry
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessian
        (unitTransverseInflateFamily (K := K) P) i j =
      MvPolynomial.C
          (unitTransverseDerivativeCoefficient (K := K) i *
            unitTransverseDerivativeCoefficient (K := K) j) *
        unitTransverseInflateFamily (K := K)
          (HC4.Polynomial.hessian P i j) := by
  unfold unitTransverseInflateFamily
  rw [hessian_kernelInflateHom_entry]
  rw [hessian_kernelInflateHom_entry]
  rw [hessian_kernelInflateHom_entry]
  simp only [map_mul, kernelInflateHom_C]
  fin_cases i <;> fin_cases j <;>
    simp [unitTransverseDerivativeCoefficient,
      kernelInflateDerivativeCoefficient] <;> ring

/-- **Full four-block inflation covariance.**

Whenever the first two permuted directions are transverse, the first
complement is `x₀`, and the second complement is transverse, simultaneous
transverse inflation is exactly diagonal congruence by `(tau,tau|1,tau)`
after applying the canonical inflation homomorphism to the old entries. -/
theorem permutedPolynomialHessianFourBlock_unitTransverseInflateFamily
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0) :
    permutedPolynomialHessianFourBlock rho
        (unitTransverseInflateFamily (K := K) P) =
      ((permutedPolynomialHessianFourBlock rho P).map
          (unitTransverseInflateRingHom (K := K))).diagonalScale
        (MvPolynomial.C (Polynomial.X : Polynomial K))
        (MvPolynomial.C (Polynomial.X : Polynomial K))
        1
        (MvPolynomial.C (Polynomial.X : Polynomial K)) := by
  apply GeneralFourBlock.ext <;>
    simp only [permutedPolynomialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Matrix.submatrix_apply,
      GeneralFourBlock.map, GeneralFourBlock.diagonalScale]
  all_goals
    rw [hessian_unitTransverseInflateFamily_entry]
    simp [unitTransverseDerivativeCoefficient, hzero, hone, htwo, hthree,
      unitTransverseInflateRingHom_apply] <;> ring

/-- The first cleared quotient entry acquires exactly `tau^4`. -/
theorem permutedPolynomialHessianFourBlock_schurA_unitTransverseInflateFamily
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0) :
    (permutedPolynomialHessianFourBlock rho
        (unitTransverseInflateFamily (K := K) P)).schurA =
      (MvPolynomial.C (Polynomial.X : Polynomial K)) ^ 4 *
        unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurA := by
  rw [permutedPolynomialHessianFourBlock_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  rw [GeneralFourBlock.schurA_diagonalScale]
  rw [GeneralFourBlock.schurA_map]
  rw [unitTransverseInflateRingHom_apply]
  ring

/-- The mixed cleared quotient entry acquires exactly `tau^5`. -/
theorem permutedPolynomialHessianFourBlock_schurB_unitTransverseInflateFamily
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0) :
    (permutedPolynomialHessianFourBlock rho
        (unitTransverseInflateFamily (K := K) P)).schurB =
      (MvPolynomial.C (Polynomial.X : Polynomial K)) ^ 5 *
        unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurB := by
  rw [permutedPolynomialHessianFourBlock_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  rw [GeneralFourBlock.schurB_diagonalScale]
  rw [GeneralFourBlock.schurB_map]
  rw [unitTransverseInflateRingHom_apply]
  ring

/-- The second cleared quotient entry acquires exactly `tau^6`. -/
theorem permutedPolynomialHessianFourBlock_schurC_unitTransverseInflateFamily
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0) :
    (permutedPolynomialHessianFourBlock rho
        (unitTransverseInflateFamily (K := K) P)).schurC =
      (MvPolynomial.C (Polynomial.X : Polynomial K)) ^ 6 *
        unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurC := by
  rw [permutedPolynomialHessianFourBlock_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  rw [GeneralFourBlock.schurC_diagonalScale]
  rw [GeneralFourBlock.schurC_map]
  rw [unitTransverseInflateRingHom_apply]
  ring

/-- Consequently the cleared quotient determinant acquires exactly `tau^10`. -/
theorem permutedPolynomialHessianFourBlock_schurDetCore_unitTransverseInflateFamily
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0) :
    (permutedPolynomialHessianFourBlock rho
        (unitTransverseInflateFamily (K := K) P)).schurDetCore =
      (MvPolynomial.C (Polynomial.X : Polynomial K)) ^ 10 *
        unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).schurDetCore := by
  rw [permutedPolynomialHessianFourBlock_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  rw [GeneralFourBlock.schurDetCore_diagonalScale]
  rw [GeneralFourBlock.schurDetCore_map]
  rw [unitTransverseInflateRingHom_apply]
  ring

end

end HC4.Valuation
