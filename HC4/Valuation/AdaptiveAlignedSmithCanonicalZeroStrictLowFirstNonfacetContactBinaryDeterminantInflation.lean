import HC4.Newton.GeneralFourBlockDeterminantCovariance
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurInflation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryInflationInjective
import Mathlib.Tactic

/-!
# A19.R18: exact full-determinant factor under binary transverse inflation

For every closing cyclic order, simultaneous unit inflation of the three
transverse source coordinates is diagonal congruence by

    (tau, tau | 1, tau).

The full four-by-four determinant therefore acquires exactly six parameter
factors.  This is the determinant-level counterpart of the already-green
`tau^4`, `tau^5`, `tau^6`, and `tau^10` Schur-entry identities.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The full permuted Hessian determinant acquires exactly `tau^6` under
simultaneous unit transverse inflation. -/
theorem permutedPolynomialHessianFourBlock_determinantCore_unitTransverseInflateFamily
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0) :
    (permutedPolynomialHessianFourBlock rho
        (unitTransverseInflateFamily (K := K) P)).determinantCore =
      (MvPolynomial.C (Polynomial.X : Polynomial K)) ^ 6 *
        unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P).determinantCore := by
  rw [permutedPolynomialHessianFourBlock_unitTransverseInflateFamily
    rho P hzero hone htwo hthree]
  rw [GeneralFourBlock.determinantCore_diagonalScale]
  rw [GeneralFourBlock.determinantCore_map]
  rw [unitTransverseInflateRingHom_apply]
  ring

end

end HC4.Valuation
