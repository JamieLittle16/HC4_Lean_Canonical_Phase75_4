import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrLeadingSelfCoefficient
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyActiveConstant
import Mathlib.Tactic

/-!
# The first PR exposure controls the whole contact carrier

The first auxiliary coordinate for `.qs` is coordinate `1`.  Its support
inequality survives the subsequent two refinements.  At a surviving `.pr`
endpoint the two retained `(0,1)` pairs are `(0,1)` and `(1,0)`, so this
inequality says `d 0 + d 1 ≤ 1` for EVERY monomial of the contact face.

Consequently the actual contact carrier is affine in these two coordinates.
This is stronger than the degree-one statement for the final ray.  In
particular every longitudinal coefficient of degree at least two enters at
positive contact order.  R18.38 then proves that the leading parameter
residual is nonzero.  A closing argument must retain its cancellation with
the full coupling correction.
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
variable {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}

/-- The first secondary exposure bounds the whole honest contact face. -/
theorem pr_contact_support_pair_le_one
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ C.face.support) :
    d (0 : Fin 4) + d (1 : Fin 4) ≤ 1 := by
  have h := C.ray.first_auxiliary_support_bound d hd
  have hv := (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have ho := C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have ho1 := ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  simp [crossFacetRayAux0, HC4.Polynomial.facetOmittedCoordinate] at h
  rw [hv, ho, ho1] at h
  norm_num at h
  omega

/-- Longitudinal degrees at least two are absent from the entire contact face. -/
theorem pr_contact_longitudinal_coeff_eq_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (n : ℕ) (hn : 2 ≤ n) :
    (MvPolynomial.finSuccEquiv K 3 C.face).coeff n = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_zero]
  by_contra hne
  have h := C.pr_contact_support_pair_le_one hthree houtThree
    (MvPolynomial.mem_support_iff.mpr hne)
  have h0 : (Finsupp.cons n m) (0 : Fin 4) = n := by simp
  rw [h0] at h
  omega

/-- The leading source slice has strictly positive CONTACT order, with no
identification of the contact and ray clocks. -/
theorem QsOtherFacetContactPrExtremalDegreeData.pr_qN_pos
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    0 < E.qN := by
  by_contra hnot
  have hq : E.qN = 0 := by omega
  have hlead := E.contactLeadingParameterLayer_eq
  rw [hq] at hlead
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer at hlead
  rw [familyParameterLayer_zero_eq_polynomialFamilySpecialFiber,
    P.contactFamily_specialFiber_eq_face,
    C.pr_contact_longitudinal_coeff_eq_zero hthree houtThree E.next.N E.N_two_le] at hlead
  exact E.leading.slice_ne_zero hlead.symm

/-- The leading parameter residual cannot be discarded in the surviving PR
geometry: its exact coefficient is nonzero. -/
theorem QsOtherFacetContactPrExtremalDegreeData.pr_contactLeadingParameterResidualLayer_ne_zero
    (E : QsOtherFacetContactPrExtremalDegreeData R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (MvPolynomial.finSuccEquiv K 3
      (familyParameterLayer P.contactProfileParameterResidual
        (E.qN + E.qN))).coeff (E.next.N + E.next.N) ≠ 0 := by
  intro hzero
  have hq := E.contactLeadingParameterResidualLayer_eq_zero_iff.mp hzero
  have hpos := E.pr_qN_pos hthree houtThree
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
