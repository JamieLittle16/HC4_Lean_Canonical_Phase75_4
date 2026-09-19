import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryHomogenization
import HC4.Valuation.SeparatedRightWallScaleDescent
import HC4.Valuation.PermutedFamilyHessianFourBlock
import Mathlib.Tactic

/-!
# A19.128: exact Schur clock on the binary-homogenized contact family

A19.123 performs the three simultaneous transverse source inflations that turn
the canonical contact grading into the pure binary grading

    tau-order = D - profileWeight * longitudinalDegree.

The generic transverse-inflation covariance theorem already proves that three
such source inflations raise the four-dimensional Hessian determinant clock by
exactly six.  Therefore the binary-homogenized contact family still has a pure
parameter Hessian clock, now at

    (4*D - 2*(contactGap+4)) + 6.

Applying the state-free permuted four-block Schur identity then gives the exact
denominator-cleared Schur clock for every simultaneous source-coordinate
permutation.  This is the determinant-side input for the final coefficientwise
identification with the stationary binary profile Hessian.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The binary-homogenized contact family inherits the exact contact Hessian
clock, shifted by six from the three unit transverse source inflations. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_hessianDefect
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    HasPolynomialFamilyHessianDefect (K := K)
      P.binaryHomogenizedFamily
      ((4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6) := by
  exact
    unitTransverseInflateFamily_hasHessianDefect_add_six
      P.contactFamily P.hessianDefect

/-- Every coordinate-permuted cleared Schur block of the binary-homogenized
contact family has the same shifted exact determinant clock. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_permutedSchurDetCore_eq_activeDet_mul_X_pow
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    let H := permutedFamilyHessianFourBlock rho P.binaryHomogenizedFamily
    H.schurDetCore =
      H.activeDet *
        (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^
          ((4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6) := by
  dsimp only
  rw [GeneralFourBlock.schurDetCore_eq_activeDet_mul_determinantCore]
  rw [permutedFamilyHessianFourBlock_determinantCore_eq_X_pow
    rho P.binaryHomogenizedFamily P.binaryHomogenized_hessianDefect]

/-- Consequently every cleared-Schur coefficient strictly before the shifted
binary determinant clock is zero. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_permutedSchurDetCore_coeff_eq_zero_of_lt
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    {n : ℕ}
    (hn : n < (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6) :
    ((permutedFamilyHessianFourBlock rho P.binaryHomogenizedFamily).schurDetCore).coeff n = 0 := by
  rw [P.binaryHomogenized_permutedSchurDetCore_eq_activeDet_mul_X_pow rho]
  rw [Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le_of_lt hn]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
