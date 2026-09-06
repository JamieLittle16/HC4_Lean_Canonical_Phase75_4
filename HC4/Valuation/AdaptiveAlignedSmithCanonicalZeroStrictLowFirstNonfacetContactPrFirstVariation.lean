import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrAffineHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactWeightedSchurShear
import Mathlib.Tactic

/-!
# First determinant variation on the actual affine PR contact carrier

The zero complementary block and zero mixed determinant remove all first-order
variations except the complementary Hessian entries paired with the constant
bordered minors. The genuine determinant clock kills their sum. No constant
kernel, vanishing raw complementary determinant, or product clock is assumed.
This is a necessary equation for the actual terminal family, not a terminal
contradiction. Later coefficients still contain nonlinear convolution terms.
-/

namespace HC4.Newton.GeneralFourBlock

variable {R : Type*} [CommRing R]

/-- First variation at a zero complementary block with singular mixed block.
The constant bordered minors remain attached to their original carrier. -/
theorem coeff_one_determinant_of_zero_complement
    (H : GeneralFourBlock (Polynomial R))
    (hx : H.x.coeff 0 = 0) (hy : H.y.coeff 0 = 0)
    (hz : H.z.coeff 0 = 0)
    (hm : (H.p * H.s - H.q * H.r).coeff 0 = 0) :
    H.x.coeff 1 * H.schurC.coeff 0 +
        H.z.coeff 1 * H.schurA.coeff 0 -
        2 * H.y.coeff 1 * H.schurB.coeff 0 =
      H.determinantCore.coeff 1 := by
  have h := congrArg (fun f : Polynomial R => f.coeff 1)
    H.activeDet_mul_rawComplementDet_eq_schur_coupling_correction
  have hraw0 : (H.x * H.z - H.y * H.y).coeff 0 = 0 := by
    simp [hx, hy, hz]
  have hraw1 : (H.x * H.z - H.y * H.y).coeff 1 = 0 := by
    simp [Polynomial.mul_coeff_one, hx, hy, hz]
  have hmix1 : ((H.p * H.s - H.q * H.r)^2).coeff 1 = 0 := by
    rw [pow_two, Polynomial.mul_coeff_one, hm]
    simp
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.mul_coeff_one, hraw0, hraw1, hmix1, hx, hy, hz,
    zero_mul, mul_zero, zero_add, add_zero] at h
  norm_num at h
  linear_combination -h

end HC4.Newton.GeneralFourBlock

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

/-- The full clock imposes a first-variation equation on the actual PR family.
All constant bordered minors refer to the same retained contact Hessian. -/
theorem QsOtherFacetContactQuadraticReesPackage.pr_contact_firstVariation_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let H := permutedFamilyHessianFourBlock qsPrContactSchurPermutation P.contactFamily
    H.x.coeff 1 * H.schurC.coeff 0 +
      H.z.coeff 1 * H.schurA.coeff 0 -
      2 * H.y.coeff 1 * H.schurB.coeff 0 = 0 := by
  let H := permutedFamilyHessianFourBlock qsPrContactSchurPermutation P.contactFamily
  have hentry (i j : Fin 4) :
      ((parameterFirstHessian P.contactFamily) i j).coeff 0 =
        HC4.Polynomial.hessian C.face i j := by
    rw [parameterFirstHessian_coeff,
      familyParameterLayer_zero_eq_polynomialFamilySpecialFiber,
      P.contactFamily_specialFiber_eq_face]
  have hx : H.x.coeff 0 = 0 := by
    change ((parameterFirstHessian P.contactFamily) 0 0).coeff 0 = 0
    rw [hentry]
    exact C.pr_contact_pair_hessian_eq_zero hthree houtThree 0 0
      (Or.inl rfl) (Or.inl rfl)
  have hy : H.y.coeff 0 = 0 := by
    change ((parameterFirstHessian P.contactFamily) 0 1).coeff 0 = 0
    rw [hentry]
    exact C.pr_contact_pair_hessian_eq_zero hthree houtThree 0 1
      (Or.inl rfl) (Or.inr rfl)
  have hz : H.z.coeff 0 = 0 := by
    change ((parameterFirstHessian P.contactFamily) 1 1).coeff 0 = 0
    rw [hentry]
    exact C.pr_contact_pair_hessian_eq_zero hthree houtThree 1 1
      (Or.inr rfl) (Or.inr rfl)
  have hm : (H.p * H.s - H.q * H.r).coeff 0 = 0 := by
    simp only [Polynomial.coeff_sub, Polynomial.mul_coeff_zero]
    change ((parameterFirstHessian P.contactFamily) 2 0).coeff 0 *
        ((parameterFirstHessian P.contactFamily) 3 1).coeff 0 -
      ((parameterFirstHessian P.contactFamily) 2 1).coeff 0 *
        ((parameterFirstHessian P.contactFamily) 3 0).coeff 0 = 0
    simp_rw [hentry]
    have hsym (i j : Fin 4) :
        HC4.Polynomial.hessian C.face i j = HC4.Polynomial.hessian C.face j i :=
      pderiv_comm_backport j i C.face
    rw [hsym 2 0, hsym 3 1, hsym 2 1, hsym 3 0]
    simpa only [mul_comm] using C.pr_contact_mixedDet_eq_zero hthree houtThree
  change H.x.coeff 1 * H.schurC.coeff 0 +
    H.z.coeff 1 * H.schurA.coeff 0 -
    2 * H.y.coeff 1 * H.schurB.coeff 0 = 0
  rw [H.coeff_one_determinant_of_zero_complement hx hy hz hm]
  have hclock := permutedFamilyHessianFourBlock_determinantCore_eq_X_pow
    qsPrContactSchurPermutation P.contactFamily P.hessianDefect
  change H.determinantCore = _ at hclock
  rw [hclock, Polynomial.coeff_X_pow]
  have hmargin := P.two_level_lt_defect
  have hlarge : 1 < 4 * T.topFace.degree - 2 * (P.contactGap + 4) := by
    omega
  simp [Nat.ne_of_gt hlarge, Ne.symm (Nat.ne_of_gt hlarge)]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation
