import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDeterminantExtraction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryActiveSchur
import Mathlib.Tactic

/-!
# A19.R18: binary profile-Hessian parameter support lies below the clock

The whole binary profile-Hessian determinant is supported only at parameter
orders

    2D - r*n.

Hence its parameter-first polynomial has degree at most `2D`.  The existing
strict binary Hessian margin puts `2D` strictly below the closing clock.  This
is exactly the support hypothesis required by bounded constant-pivot
cancellation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- No parameter layer of the binary profile-Hessian determinant occurs above
`2D`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessianDetFamily_parameterLayer_eq_zero_of_two_mul_degree_lt
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {q : ℕ}
    (hq : 2 * T.topFace.degree < q) :
    familyParameterLayer P.binaryProfileHessianDetFamily q = 0 := by
  apply (MvPolynomial.finSuccEquiv K 3).injective
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro m
  rw [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [familyParameterLayer_coeff]
  have hlong := R.binaryProfileHessianDetFamily_longitudinal_coeff n
  have hm := congrArg
    (fun A : MvPolynomial (Fin 3) (Polynomial K) => MvPolynomial.coeff m A)
    hlong
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hm
  rw [hm]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rw [Polynomial.coeff_X_pow_mul']
  have hslt :
      2 * T.topFace.degree - P.profileWeight * n < q :=
    lt_of_le_of_lt (Nat.sub_le _ _) hq
  have hsle :
      2 * T.topFace.degree - P.profileWeight * n ≤ q :=
    Nat.le_of_lt hslt
  have hpos :
      0 < q - (2 * T.topFace.degree - P.profileWeight * n) :=
    Nat.sub_pos_of_lt hslt
  simp [hsle, Nat.ne_of_gt hpos]

/-- The parameter-first binary profile-Hessian determinant has degree at most
`2D`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.parameterFirst_binaryProfileHessianDetFamily_natDegree_le
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    (parameterFirstEquiv K P.binaryProfileHessianDetFamily).natDegree ≤
      2 * T.topFace.degree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro q hq
  rw [parameterFirstEquiv_coeff]
  exact R.binaryProfileHessianDetFamily_parameterLayer_eq_zero_of_two_mul_degree_lt hq

/-- In particular the entire binary profile-Hessian determinant lies strictly
below the exact binary Hessian closing clock. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.parameterFirst_binaryProfileHessianDetFamily_natDegree_lt_hessianClock
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    (parameterFirstEquiv K P.binaryProfileHessianDetFamily).natDegree <
      (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6 := by
  have hclock := P.binary_profileOrder_lt_hessianClock R 0
  simp only [Nat.mul_zero, Nat.sub_zero] at hclock
  exact lt_of_le_of_lt
    R.parameterFirst_binaryProfileHessianDetFamily_natDegree_le hclock

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
