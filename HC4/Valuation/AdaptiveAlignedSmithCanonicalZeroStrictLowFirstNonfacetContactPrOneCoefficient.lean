import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrAffineCarrier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFractionProfileRigidity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianDegreeBound
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryProfileHessianCancellation
import Mathlib.Tactic

/-!
# One exposed product coefficient suffices in the surviving PR branch

The affine contact carrier proves `qN > 0`.  The first staircase coefficient
alone forces `D = N*r` if it vanishes.  The retained leading grading equation
then contradicts `qN > 0`; the next coefficient is unnecessary in this branch.

The product-zero premise remains a genuine mathematical obligation.  This
module does not derive it from the full Hessian determinant equation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

/-- A zero leading profile-Hessian coefficient is already contradictory in
the surviving PR branch. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.pr_impossible_of_leading_profileHessianDet_coeff
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hzero : R.profileHessianDet.coeff (E.next.N + E.next.N) = 0) : False := by
  let A := MvPolynomial (Fin 3) K
  let L := qsContactProfileField K
  let ι : A →+* L := algebraMap A L
  have hι : Function.Injective ι := IsFractionRing.injective A L
  let h := Polynomial.map ι R.profile
  have hdegree : h.natDegree = E.next.N := by
    dsimp [h]
    rw [Polynomial.natDegree_map_eq_of_injective hι R.profile]
    exact E.next.N_eq.symm
  have hp : R.profile ≠ 0 := by
    intro hz
    have hc := R.coeff_zero_ne
    rw [hz] at hc
    simp at hc
  have hc : h.coeff E.next.N ≠ 0 := by
    dsimp [h]
    rw [Polynomial.coeff_map, E.next.N_eq, Polynomial.coeff_natDegree]
    intro hz
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
      (hι (by simpa using hz))
  have hz :
      (binaryStaircaseProfileResidual T.topFace.degree P.profileWeight h).coeff
        (E.next.N + E.next.N) = 0 := by
    rw [show h = Polynomial.map ι R.profile from rfl,
      ← R.fractionMap_profileHessianDet_eq_residual,
      Polynomial.coeff_map, hzero, map_zero]
  rw [coeff_add_self_binaryStaircaseProfileResidual
    T.topFace.degree P.profileWeight E.next.N h (by omega)] at hz
  have hs := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hc)
  have hboundary := binaryStaircaseProfile_boundary_of_leadingScalar_eq_zero
    (K := L) T.topFace.degree P.profileWeight E.next.N E.N_two_le
    (by rw [E.next.N_eq]; exact R.support_bound) hs
  have hgrade := E.leading_grade
  have hpositive := E.pr_qN_pos hthree houtThree
  rw [Nat.mul_comm E.next.N P.profileWeight] at hboundary
  omega

/-- **Single-coefficient PR terminal consumer.**  Only the leading active
pivot/profile product coefficient must be supplied.  The old next-pair
calculation is not needed for this conditional contradiction. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.pr_impossible_of_leading_profilePivotProduct_coeff
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hprod :
      ((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation P.contactFamily).activeDet *
        parameterFirstEquiv K P.binaryProfileHessianDetFamily).coeff
          (2 * T.topFace.degree -
            P.profileWeight * (E.next.N + E.next.N)) = 0) : False := by
  let A := (permutedFamilyHessianFourBlock
    qsPrSuperfaceSchurPermutation P.contactFamily).activeDet
  let B := parameterFirstEquiv K P.binaryProfileHessianDetFamily
  have hA0 : A.coeff 0 ≠ 0 :=
    P.pr_contactFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  have hb := polynomial_coeff_eq_zero_of_constant_pivot A B hA0 hprod
    (fun k hk => by
      dsimp [B]
      rw [parameterFirstEquiv_coeff]
      exact R.binaryProfileHessianDetFamily_parameterLayer_eq_zero_of_lt_qNN
        (by simpa [E.next.N_eq] using hk))
  have hlayer : familyParameterLayer P.binaryProfileHessianDetFamily
      (2 * T.topFace.degree - P.profileWeight * (E.next.N + E.next.N)) = 0 := by
    simpa only [B, parameterFirstEquiv_coeff] using hb
  exact R.pr_impossible_of_leading_profileHessianDet_coeff E hthree houtThree
    (R.profileHessianDet_coeff_eq_zero_of_binaryFamily_layer
      (E.next.N + E.next.N) hlayer)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
