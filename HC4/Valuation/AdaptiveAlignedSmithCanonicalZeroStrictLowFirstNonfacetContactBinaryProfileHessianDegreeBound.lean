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

R18.21 additionally needs the opposite, extremal end of the same support
calculation.  If `N` is the highest longitudinal profile index, every profile
Hessian entry still has longitudinal degree at most `N`, hence its determinant
has degree at most `2N`.  Consequently the exact binary determinant family has
no parameter support below

    qNN = 2D - r(2N).

This is the first triangularity fact needed for the two exposed staircase
coefficients; it does not assert any Schur-to-profile implication.
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

/-- The parameter-parameter profile Hessian entry has no longitudinal support
above the raw profile. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian00_natDegree_le_profile
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    R.profileHessian00.natDegree ≤ R.profile.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [R.coeff_profileHessian00]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  simp

/-- The mixed profile Hessian entry has no longitudinal support above the raw
profile. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian01_natDegree_le_profile
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    R.profileHessian01.natDegree ≤ R.profile.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [R.coeff_profileHessian01]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  simp

/-- The longitudinal profile Hessian entry has no longitudinal support above
the raw profile. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessian11_natDegree_le_profile
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    R.profileHessian11.natDegree ≤ R.profile.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [R.coeff_profileHessian11]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  simp

/-- Therefore the integral profile-Hessian determinant is supported in
longitudinal degree at most twice the profile degree. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet_natDegree_le_two_profile
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    R.profileHessianDet.natDegree ≤ R.profile.natDegree + R.profile.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [QsOtherFacetContactRawLongitudinalProfilePackage.profileHessianDet,
    Polynomial.coeff_sub]
  have h0011 :
      (R.profileHessian00 * R.profileHessian11).natDegree ≤
        R.profile.natDegree + R.profile.natDegree :=
    le_trans Polynomial.natDegree_mul_le
      (Nat.add_le_add R.profileHessian00_natDegree_le_profile
        R.profileHessian11_natDegree_le_profile)
  have h0101 :
      (R.profileHessian01 * R.profileHessian01).natDegree ≤
        R.profile.natDegree + R.profile.natDegree :=
    le_trans Polynomial.natDegree_mul_le
      (Nat.add_le_add R.profileHessian01_natDegree_le_profile
        R.profileHessian01_natDegree_le_profile)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h0011 hn),
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h0101 hn)]
  simp

/-- **R18.21 first exposed parameter order.**  If `N` is the highest raw
longitudinal profile index, the whole binary profile-Hessian determinant has no
parameter layer below `qNN = 2D-r(2N)`.  This is the lower-support companion to
the `2D` upper degree bound below. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessianDetFamily_parameterLayer_eq_zero_of_lt_qNN
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {q : ℕ}
    (hq : q <
      2 * T.topFace.degree -
        P.profileWeight * (R.profile.natDegree + R.profile.natDegree)) :
    familyParameterLayer P.binaryProfileHessianDetFamily q = 0 := by
  apply (MvPolynomial.finSuccEquiv K 3).injective
  simp only [map_zero]
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro m
  rw [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [familyParameterLayer_coeff]
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [R.binaryProfileHessianDetFamily_longitudinal_coeff n]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  by_cases hn : n ≤ R.profile.natDegree + R.profile.natDegree
  · have hmul :
        P.profileWeight * n ≤
          P.profileWeight * (R.profile.natDegree + R.profile.natDegree) :=
      Nat.mul_le_mul_left P.profileWeight hn
    have horder :
        2 * T.topFace.degree -
            P.profileWeight * (R.profile.natDegree + R.profile.natDegree) ≤
          2 * T.topFace.degree - P.profileWeight * n :=
      Nat.sub_le_sub_left hmul (2 * T.topFace.degree)
    have hqorder :
        q < 2 * T.topFace.degree - P.profileWeight * n :=
      lt_of_lt_of_le hq horder
    rw [Polynomial.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hqorder]
  · have hnlt :
        R.profile.natDegree + R.profile.natDegree < n :=
      Nat.lt_of_not_ge hn
    have hdet : R.profileHessianDet.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt R.profileHessianDet_natDegree_le_two_profile hnlt)
    rw [hdet]
    simp

/-- No parameter layer of the binary profile-Hessian determinant occurs above
`2D`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.binaryProfileHessianDetFamily_parameterLayer_eq_zero_of_two_mul_degree_lt
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {q : ℕ}
    (hq : 2 * T.topFace.degree < q) :
    familyParameterLayer P.binaryProfileHessianDetFamily q = 0 := by
  apply (MvPolynomial.finSuccEquiv K 3).injective
  simp only [map_zero]
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro m
  rw [Polynomial.coeff_zero, MvPolynomial.coeff_zero]
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [familyParameterLayer_coeff]
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [R.binaryProfileHessianDetFamily_longitudinal_coeff n]
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
