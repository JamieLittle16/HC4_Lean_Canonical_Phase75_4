import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarAffineRR
import Mathlib.Tactic

/-!
# A19 primitive highest planar slice

The source-honest highest pair slice is now a genuine affine-RR ray.  Its three
transverse slopes are the locked source-ray coordinate differences.  Every one
of those differences is strictly negative, so none vanishes; moreover

    1 + q + r + s < 0.

Hence the exceptional factor in the already-certified rank-three highest
relation is nonzero.  `LineSupportedHessianRigidity` therefore forces the
coefficient polynomial to have natural degree exactly one.  The affine-RR
coefficient/exponent correspondence then identifies the actual multivariate
slice support with precisely its adjacent coordinate-`0` layers `0` and `1`.

This is the Lean-facing version of the paper statement that every nontrivial
highest singular line slice is primitive.  No balance equation and no JC2
hypothesis is used.
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

/-- The affine-RR slope direction of a source-honest highest slice avoids the
only exceptional factor in the rank-three highest-direction relation. -/
theorem QsOtherFacetPlanarAffineRRPackage.direction_factor_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C next P}
    (A : QsOtherFacetPlanarAffineRRPackage C next P S)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    A.ray.zeroSlope 1 * A.ray.zeroSlope 2 * A.ray.zeroSlope 3 *
        (1 + A.ray.zeroSlope 1 + A.ray.zeroSlope 2 + A.ray.zeroSlope 3) ≠ 0 := by
  let d1 : ℤ :=
    (C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ)
  let d2 : ℤ :=
    (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ)
  let d3 : ℤ :=
    (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ)
  have hsigns := C.qs_ray_otherFacet_locked_direction_signs
    hthree hne houtThree
  have hd1neg : d1 < 0 := by
    dsimp [d1]
    exact_mod_cast hsigns.2.2 (1 : Fin 4) (by decide)
  have hd2neg : d2 < 0 := by
    dsimp [d2]
    exact_mod_cast hsigns.2.2 (2 : Fin 4) (by decide)
  have hd3neg : d3 < 0 := by
    dsimp [d3]
    exact_mod_cast hsigns.2.2 (3 : Fin 4) (by decide)
  have hd1ne : d1 ≠ 0 := ne_of_lt hd1neg
  have hd2ne : d2 ≠ 0 := ne_of_lt hd2neg
  have hd3ne : d3 ≠ 0 := ne_of_lt hd3neg
  have hsumneg : (1 : ℤ) + d1 + d2 + d3 < 0 := by omega
  have hsumne : (1 : ℤ) + d1 + d2 + d3 ≠ 0 := ne_of_lt hsumneg
  have hd1K : (d1 : K) ≠ 0 := by exact_mod_cast hd1ne
  have hd2K : (d2 : K) ≠ 0 := by exact_mod_cast hd2ne
  have hd3K : (d3 : K) ≠ 0 := by exact_mod_cast hd3ne
  have hsumK0 : (((1 : ℤ) + d1 + d2 + d3 : ℤ) : K) ≠ 0 := by
    exact_mod_cast hsumne
  have hsumK : (1 : K) + (d1 : K) + (d2 : K) + (d3 : K) ≠ 0 := by
    simpa only [Int.cast_add, Int.cast_one] using hsumK0
  rw [A.slope_eq_locked (1 : Fin 4),
    A.slope_eq_locked (2 : Fin 4),
    A.slope_eq_locked (3 : Fin 4)]
  change (d1 : K) * (d2 : K) * (d3 : K) *
      ((1 : K) + (d1 : K) + (d2 : K) + (d3 : K)) ≠ 0
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd1K hd2K) hd3K) hsumK

/-- The coefficient polynomial of any nontrivial source-honest highest slice
has degree exactly one. -/
theorem QsOtherFacetPlanarAffineRRPackage.coefficient_natDegree_eq_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C next P}
    (A : QsOtherFacetPlanarAffineRRPackage C next P S)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    A.ray.zeroCoefficientPolynomial.natDegree = 1 := by
  let L := A.ray.zeroAffineLineData
  have hA : 0 < A.ray.facetExponent 1 :=
    A.facet_transverse_pos 1 (by decide)
  have hB : 0 < A.ray.facetExponent 2 :=
    A.facet_transverse_pos 2 (by decide)
  have hC : 0 < A.ray.facetExponent 3 :=
    A.facet_transverse_pos 3 (by decide)
  have hphiDeg : 0 < A.ray.zeroCoefficientPolynomial.natDegree :=
    A.ray.zeroCoefficientPolynomial_natDegree_pos
  have hphi0 : A.ray.zeroCoefficientPolynomial.coeff 0 ≠ 0 :=
    A.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hdir := A.direction_factor_ne_zero hthree hne houtThree
  have hdet : hessianDeterminant L.polynomial = 0 := by
    dsimp [L]
    exact A.ray.zeroAffineLineData_hessian_zero S.hessian_zero
  exact HC4.RationalRigidity.affine_line_natDegree_eq_one_of_direction_factor_ne_zero
    L hA hB hC (by norm_num) hphiDeg hphi0 hdir hdet

/-- The univariate coefficient support of a nontrivial highest slice is
exactly the two adjacent indices `{0,1}`. -/
theorem QsOtherFacetPlanarAffineRRPackage.coefficient_support_eq_zero_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C next P}
    (A : QsOtherFacetPlanarAffineRRPackage C next P S)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    A.ray.zeroCoefficientPolynomial.support = {0, 1} := by
  let phi := A.ray.zeroCoefficientPolynomial
  have hphi0 : phi.coeff 0 ≠ 0 := by
    dsimp [phi]
    exact A.ray.zeroCoefficientPolynomial_coeff_zero_ne
  have hphiNe : phi ≠ 0 := by
    intro hzero
    subst phi
    simp at hphi0
  have hdeg : phi.natDegree = 1 := by
    dsimp [phi]
    exact A.coefficient_natDegree_eq_one hthree hne houtThree
  have hphi1 : phi.coeff 1 ≠ 0 := by
    have hlead : phi.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hphiNe
    rw [← hdeg]
    rw [Polynomial.coeff_natDegree]
    exact hlead
  ext n
  constructor
  · intro hn
    have hnle : n ≤ phi.natDegree :=
      Polynomial.le_natDegree_of_mem_supp n hn
    rw [hdeg] at hnle
    interval_cases n <;> simp
  · intro hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact Polynomial.mem_support_iff.mpr hphi0
    · exact Polynomial.mem_support_iff.mpr hphi1

/-- **Primitive highest slice.**  The actual multivariate support of a
nontrivial highest pair slice consists of exactly the two source-honest
adjacent affine-RR exponents at coordinate-`0` indices `0` and `1`. -/
theorem QsOtherFacetPlanarAffineRRPackage.slice_support_eq_primitive_pair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C next P}
    (A : QsOtherFacetPlanarAffineRRPackage C next P S)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    S.slice.support =
      {A.ray.zeroExponentAt 0, A.ray.zeroExponentAt 1} := by
  have hphi := A.coefficient_support_eq_zero_one hthree hne houtThree
  ext d
  constructor
  · intro hd
    have hdFace : d ∈ A.ray.face.support := by
      rw [A.face_eq]
      exact hd
    have hidx := A.ray.zeroCoefficientPolynomial_mem_of_face_mem hdFace
    rw [hphi] at hidx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hidx
    rcases hidx with hd0 | hd1
    · have hexp := A.ray.zeroExponentAt_eq_of_face_mem hdFace
      rw [hd0] at hexp
      simp [hexp]
    · have hexp := A.ray.zeroExponentAt_eq_of_face_mem hdFace
      rw [hd1] at hexp
      simp [hexp]
  · intro hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · have h0phi : 0 ∈ A.ray.zeroCoefficientPolynomial.support := by
        rw [hphi]
        simp
      rcases A.ray.exists_faceExponent_of_zeroCoefficientPolynomial_mem h0phi with
        ⟨e, he, he0⟩
      have hs := A.ray.zeroExponentAt_spec ⟨e, he, he0⟩
      rw [← A.face_eq]
      exact hs.1
    · have h1phi : 1 ∈ A.ray.zeroCoefficientPolynomial.support := by
        rw [hphi]
        simp
      rcases A.ray.exists_faceExponent_of_zeroCoefficientPolynomial_mem h1phi with
        ⟨e, he, he1⟩
      have hs := A.ray.zeroExponentAt_spec ⟨e, he, he1⟩
      rw [← A.face_eq]
      exact hs.1

/-- Direct source-facing primitive-slice entry. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.primitive_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ A : QsOtherFacetPlanarAffineRRPackage C next P S,
      S.slice.support =
        {A.ray.zeroExponentAt 0, A.ray.zeroExponentAt 1} := by
  rcases S.affineRRPackage_of_nontrivial
      hthree hne houtThree hnontrivial with ⟨A⟩
  exact ⟨A, A.slice_support_eq_primitive_pair hthree hne houtThree⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
