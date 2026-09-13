import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrPrimitiveEndpoint
import Mathlib.Tactic

/-!
# A19 exact primitive PR highest-slice normal form

This file packages the actual two source monomials of the nontrivial highest
`.pr` pair slice after the primitive endpoint classification.  It is the
source-honest version of the paper pair

    (0,n,1,V*n), (1,n-1,0,V*(n-1)),   n >= 2,

up to swapping the two transverse coordinates.
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

/-- **Actual highest-slice two-monomial normal form.**  The conclusion names
literal exponents in `S.slice.support`; no abstract replacement polynomial is
introduced. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_highest_slice_normal_form_of_nontrivial
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    (∃ n V : ℕ, ∃ e0 e1 : Fin 4 →₀ ℕ,
      2 ≤ n ∧ 0 < V ∧
      S.slice.support = {e0, e1} ∧
      e0 0 = 0 ∧ e0 1 = n ∧ e0 2 = 1 ∧ e0 3 = V * n ∧
      e1 0 = 1 ∧ e1 1 = n - 1 ∧ e1 2 = 0 ∧ e1 3 = V * (n - 1)) ∨
    (∃ n V : ℕ, ∃ e0 e1 : Fin 4 →₀ ℕ,
      2 ≤ n ∧ 0 < V ∧
      S.slice.support = {e0, e1} ∧
      e0 0 = 0 ∧ e0 1 = n ∧ e0 2 = V * n ∧ e0 3 = 1 ∧
      e1 0 = 1 ∧ e1 1 = n - 1 ∧ e1 2 = V * (n - 1) ∧ e1 3 = 0) := by
  rcases S.pr_endpoint_orientation_of_nontrivial
      hthree houtThree hnontrivial with ⟨D, A, horient⟩
  let e0 : Fin 4 →₀ ℕ := A.ray.zeroExponentAt 0
  let e1 : Fin 4 →₀ ℕ := A.ray.zeroExponentAt 1
  have hsupp : S.slice.support = {e0, e1} := by
    dsimp [e0, e1]
    exact A.slice_support_eq_primitive_pair hthree
      (by decide : (.pr : ToricFacet) ≠ .qs) houtThree

  have he0face : e0 ∈ A.ray.face.support := by
    have hzero : A.ray.facetExponent (0 : Fin 4) = 0 :=
      A.ray.facet_coordinate_zero
    have heq := A.ray.zeroExponentAt_eq_of_face_mem A.ray.facet_mem_face
    rw [hzero] at heq
    rw [heq]
    exact A.ray.facet_mem_face
  have he0zero : e0 (0 : Fin 4) = 0 := by
    have hzero : A.ray.facetExponent (0 : Fin 4) = 0 :=
      A.ray.facet_coordinate_zero
    have heq := A.ray.zeroExponentAt_eq_of_face_mem A.ray.facet_mem_face
    rw [hzero] at heq
    rw [heq]
    exact hzero

  have hcoeffSupp : A.ray.zeroCoefficientPolynomial.support = {0, 1} :=
    A.coefficient_support_eq_zero_one hthree
      (by decide : (.pr : ToricFacet) ≠ .qs) houtThree
  have h1coeff : 1 ∈ A.ray.zeroCoefficientPolynomial.support := by
    rw [hcoeffSupp]
    simp
  rcases A.ray.exists_faceExponent_of_zeroCoefficientPolynomial_mem h1coeff with
    ⟨d1, hd1face, hd10⟩
  have he1spec := A.ray.zeroExponentAt_spec ⟨d1, hd1face, hd10⟩
  have he1face : e1 ∈ A.ray.face.support := by
    simpa [e1] using he1spec.1
  have he1zero : e1 (0 : Fin 4) = 1 := by
    simpa [e1] using he1spec.2

  have he0S : e0 ∈ S.slice.support := by
    rw [hsupp]
    simp
  have he1S : e1 ∈ S.slice.support := by
    rw [hsupp]
    simp
  have hq := S.pr_quotient_eq_of_mem hthree houtThree D he0S he1S
  have hshape := primitive_pair_shape_of_quotient_eq_zero_one
    D.alpha D.beta e0 e1 hq he0zero he1zero

  have he0facet : e0 = A.ray.facetExponent := by
    have heq := A.ray.zeroExponentAt_eq_of_face_mem A.ray.facet_mem_face
    simpa [e0, A.ray.facet_coordinate_zero] using heq
  have hpair : qsOtherFacetPairDegree .pr e0 = S.pairLevel :=
    (S.support_parent_and_pairLevel he0S).2
  have he01pair : (e0 1 : ℤ) = S.pairLevel := by
    simpa [qsOtherFacetPairDegree, he0zero] using hpair
  have hnZ : (1 : ℤ) < (e0 1 : ℤ) := by
    rw [he01pair]
    exact S.pairLevel_gt_one
  have hn : 2 ≤ e0 1 := by
    exact_mod_cast hnZ

  rcases horient with hleft | hright
  · left
    have he02 : e0 2 = 1 := by
      rw [he0facet]
      simpa [hleft.2.1] using hleft.1
    have he03 : e0 3 = D.beta * e0 1 := by
      rw [he0facet]
      exact hleft.2.2
    have he11 : e1 1 = e0 1 - 1 := by omega
    have he12 : e1 2 = 0 := by omega
    have he13 : e1 3 = D.beta * (e0 1 - 1) := by
      nlinarith [hshape.2.2]
    exact ⟨e0 1, D.beta, e0, e1,
      hn, D.beta_pos, hsupp,
      he0zero, rfl, he02, by simpa [Nat.mul_comm] using he03,
      he1zero, he11, he12, by simpa using he13⟩
  · right
    have he03 : e0 3 = 1 := by
      rw [he0facet]
      simpa [hright.2.1] using hright.1
    have he02 : e0 2 = D.alpha * e0 1 := by
      rw [he0facet]
      exact hright.2.2
    have he11 : e1 1 = e0 1 - 1 := by omega
    have he13 : e1 3 = 0 := by omega
    have he12 : e1 2 = D.alpha * (e0 1 - 1) := by
      nlinarith [hshape.2.1]
    exact ⟨e0 1, D.alpha, e0, e1,
      hn, D.alpha_pos, hsupp,
      he0zero, rfl, by simpa [Nat.mul_comm] using he02, he03,
      he1zero, he11, by simpa using he12, he13⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
