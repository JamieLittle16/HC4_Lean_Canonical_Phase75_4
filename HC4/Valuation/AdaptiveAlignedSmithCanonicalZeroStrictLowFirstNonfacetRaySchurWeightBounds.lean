import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetDirectionLock
import Mathlib.Tactic

/-!
# Complementary ray weights are below half the source level

Consumes: the actual positive ray Rees weights, strict-low source witness,
and PR endpoint direction lock.
Produces: 2*w0 < level and 2*w1 < level in the PR branch.
Next consumer: sharp parameter coefficient bounds for all three Schur entries.
This does not construct source-honest rank promotion or terminal impossibility.
-/
namespace HC4.Valuation
noncomputable section
open HC4.Newton HC4.Polynomial HC4.Toric
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}

private theorem weight_four_nat (w : Fin 4 → ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight w d = d 0 * w 0 + d 1 * w 1 + d 2 * w 2 + d 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_four, nsmul_eq_mul]

/-- The strict-low monomial has weight strictly greater than twice w0. -/
theorem QsOtherFacetRayReverseReesPackage.two_longitudinal_weight_lt_level
    (R : QsOtherFacetRayReverseReesPackage C) : 2 * R.weight 0 < R.level := by
  rcases T.strictLow_sourceCodimensionTwo_two_le with ⟨d, hd, hdeg, hd0, _⟩
  have hb := R.bound d hd
  rw [weight_four_nat] at hb
  have h0 := R.weight_pos 0
  have h1 := R.weight_pos 1
  have h2 := R.weight_pos 2
  have h3 := R.weight_pos 3
  have h1d : d 1 ≤ d 1 * R.weight 1 := by nlinarith
  have h2d : d 2 ≤ d 2 * R.weight 2 := by nlinarith
  have h3d : d 3 ≤ d 3 * R.weight 3 := by nlinarith
  change 3 ≤ d 0 + d 1 + d 2 + d 3 at hdeg
  by_cases hthree : 3 ≤ d 0
  · have hm : 3 * R.weight 0 ≤ d 0 * R.weight 0 := Nat.mul_le_mul_right _ hthree
    omega
  · have heq : d 0 = 2 := by omega
    rw [heq] at hb hdeg
    omega

/-- Every ray monomial has precisely the retained positive Rees weight. -/
theorem QsOtherFacetRayReverseReesPackage.ray_support_weight_eq_level
    (R : QsOtherFacetRayReverseReesPackage C)
    {d : Fin 4 →₀ ℕ} (hd : d ∈ C.ray.face.support) :
    Finsupp.weight R.weight d = R.level := by
  have hn := MvPolynomial.mem_support_iff.mp hd
  rw [← R.initialForm_eq_ray, coeff_initialForm] at hn
  split_ifs at hn with hw
  · rw [weight_four_nat]
    simp only [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_four, nsmul_eq_mul] at hw
    exact_mod_cast hw
  · exact (hn rfl).elim

/-- Equal endpoint ray weights and strict transverse drop force w1 < w0. -/
theorem QsOtherFacetRayReverseReesPackage.pr_omitted_weight_lt_longitudinal
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hout : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    R.weight 1 < R.weight 0 := by
  have hv := R.ray_support_weight_eq_level C.ray.facet_mem_face
  have ho := R.ray_support_weight_eq_level C.ray.outside_mem_face
  rw [weight_four_nat] at hv ho
  have hv0 := (mvRankThreeOnFacet_qs hthree).1
  have hv1 := (C.qs_ray_pr_outside_base_eq_one_and_cross hthree hout).1
  have ho0 := C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have ho1 := ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 hout).1
  rw [hv0, hv1] at hv
  rw [ho0, ho1] at ho
  simp only [zero_mul, one_mul, zero_add, add_zero] at hv ho
  have hdrop := C.qs_ray_pr_outside_strict_directionLock hthree hout
  have h2 := Nat.mul_lt_mul_of_pos_right hdrop.2.1 (R.weight_pos 2)
  have h3 := Nat.mul_lt_mul_of_pos_right hdrop.2.2 (R.weight_pos 3)
  omega

/-- Both complementary weights satisfy the strict diagonal Schur-clock margin. -/
theorem QsOtherFacetRayReverseReesPackage.pr_complementary_weights_lt_half_level
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hout : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    2 * R.weight 0 < R.level ∧ 2 * R.weight 1 < R.level := by
  have h0 := R.two_longitudinal_weight_lt_level
  have h1 := R.pr_omitted_weight_lt_longitudinal hthree hout
  constructor <;> omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation
