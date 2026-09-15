import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetNeutralSuperface
import Mathlib.Tactic

/-!
# A19 second defect-neutral other-facet skew

The paper planar-refinement argument uses a second source weight, independent
of pair degree, which is constant on the two endpoints of the locked `qs` ray
and has zero four-dimensional Hessian-clock contribution.

The paper writes the `.pr` ray as

    (0,1,kU,kV) -- (1,0,lU,lV)

and uses

    ( (k-l)(U-V), 0, 1-(k+l)V, (k+l)U-1 ).

For formalisation it is better not to introduce the auxiliary factorisation.
Writing the transverse endpoint pairs as `(B,C)` and `(Q,R)`, the already
verified direction lock gives `B*R=C*Q`, and the same weight is exactly

    ( (B-Q)-(C-R), 0, 1-C-R, B+Q-1 ).

The cyclic `.sp` and `.rq` forms are obtained by permuting the omitted
coordinate.  This file proves directly that the weight:

* has the same value on both ray endpoints;
* has coordinate sum twice that common level, hence zero Hessian-clock
  contribution;
* is genuinely independent of the pair weight.

No convex/refinement existence statement is made here; that is the next
finite-support adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Endpoint-native form of the second neutral skew. -/
def qsOtherFacetSkewWeight
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) : ToricFacet → Fin 4 → ℤ
  | .qs => ![0, 0, 0, 0]
  | .pr =>
      let B : ℤ := C.ray.facetExponent 2
      let D : ℤ := C.ray.facetExponent 3
      let Q : ℤ := C.ray.outsideExponent 2
      let R : ℤ := C.ray.outsideExponent 3
      ![(B - Q) - (D - R), 0, 1 - D - R, B + Q - 1]
  | .sp =>
      let B : ℤ := C.ray.facetExponent 1
      let D : ℤ := C.ray.facetExponent 3
      let Q : ℤ := C.ray.outsideExponent 1
      let R : ℤ := C.ray.outsideExponent 3
      ![(B - Q) - (D - R), 1 - D - R, 0, B + Q - 1]
  | .rq =>
      let B : ℤ := C.ray.facetExponent 1
      let D : ℤ := C.ray.facetExponent 2
      let Q : ℤ := C.ray.outsideExponent 1
      let R : ℤ := C.ray.outsideExponent 2
      ![(B - Q) - (D - R), 1 - D - R, B + Q - 1, 0]

/-- Common affine level of the skew on the locked ray. -/
def qsOtherFacetSkewLevel
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) : ToricFacet → ℤ
  | .qs => 0
  | .pr => (C.ray.facetExponent 2 : ℤ) - C.ray.facetExponent 3
  | .sp => (C.ray.facetExponent 1 : ℤ) - C.ray.facetExponent 3
  | .rq => (C.ray.facetExponent 1 : ℤ) - C.ray.facetExponent 2

/-- The second skew is Hessian-clock neutral: its coordinate sum is twice its
ray level. -/
theorem sum_qsOtherFacetSkewWeight_eq_two_level
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet) :
    ∑ i : Fin 4, qsOtherFacetSkewWeight C next i =
      2 * qsOtherFacetSkewLevel C next := by
  cases next <;>
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      Fin.sum_univ_four] <;> ring

private theorem weight_explicit_fin4
    (a : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight a e =
      a 0 * (e 0 : ℤ) + a 1 * (e 1 : ℤ) +
      a 2 * (e 2 : ℤ) + a 3 * (e 3 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    ring
  · intro i
    simp

/-- The skew takes its declared level on the starting `qs` endpoint. -/
theorem qsOtherFacetSkewWeight_facet_eq_level
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    Finsupp.weight (qsOtherFacetSkewWeight C next) C.ray.facetExponent =
      qsOtherFacetSkewLevel C next := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  cases next
  · have harith := C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree
    have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 := harith.1
    have hcrossZ :
        (C.ray.facetExponent 2 : ℤ) * C.ray.outsideExponent 3 =
          (C.ray.facetExponent 3 : ℤ) * C.ray.outsideExponent 2 := by
      exact_mod_cast harith.2
    rw [weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      hfacet0, hfacet1]
    nlinarith
  · have harith := C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree
    have hfacet3 : C.ray.facetExponent (3 : Fin 4) = 1 := harith.1
    have hcrossZ :
        (C.ray.facetExponent 1 : ℤ) * C.ray.outsideExponent 2 =
          (C.ray.facetExponent 2 : ℤ) * C.ray.outsideExponent 1 := by
      exact_mod_cast harith.2
    rw [weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      hfacet0, hfacet3]
    nlinarith
  · exact (hne rfl).elim
  · have harith := C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree
    have hfacet2 : C.ray.facetExponent (2 : Fin 4) = 1 := harith.1
    have hcrossZ :
        (C.ray.facetExponent 1 : ℤ) * C.ray.outsideExponent 3 =
          (C.ray.facetExponent 3 : ℤ) * C.ray.outsideExponent 1 := by
      exact_mod_cast harith.2
    rw [weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      hfacet0, hfacet2]
    nlinarith

/-- The skew takes the same level on the lower other-facet endpoint. -/
theorem qsOtherFacetSkewWeight_outside_eq_level
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    Finsupp.weight (qsOtherFacetSkewWeight C next) C.ray.outsideExponent =
      qsOtherFacetSkewLevel C next := by
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  cases next
  · have hout := (mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree
    rcases hout with ⟨hout1, _hout0, _hout2, _hout3⟩
    have harith := C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree
    have hcrossZ :
        (C.ray.facetExponent 2 : ℤ) * C.ray.outsideExponent 3 =
          (C.ray.facetExponent 3 : ℤ) * C.ray.outsideExponent 2 := by
      exact_mod_cast harith.2
    rw [weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel, hout0, hout1]
    nlinarith
  · have hout := (mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree
    rcases hout with ⟨hout3, _hout0, _hout1, _hout2⟩
    have harith := C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree
    have hcrossZ :
        (C.ray.facetExponent 1 : ℤ) * C.ray.outsideExponent 2 =
          (C.ray.facetExponent 2 : ℤ) * C.ray.outsideExponent 1 := by
      exact_mod_cast harith.2
    rw [weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel, hout0, hout3]
    nlinarith
  · exact (hne rfl).elim
  · have hout := (mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree
    rcases hout with ⟨hout2, _hout0, _hout1, _hout3⟩
    have harith := C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree
    have hcrossZ :
        (C.ray.facetExponent 1 : ℤ) * C.ray.outsideExponent 3 =
          (C.ray.facetExponent 3 : ℤ) * C.ray.outsideExponent 1 := by
      exact_mod_cast harith.2
    rw [weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel, hout0, hout2]
    nlinarith

/-- Because the locked ray has exactly its two degree-one endpoints, the skew
is constant on the whole ray support. -/
theorem qsOtherFacetSkewWeight_eq_level_of_ray_mem
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ C.ray.face.support) :
    Finsupp.weight (qsOtherFacetSkewWeight C next) e =
      qsOtherFacetSkewLevel C next := by
  have hdeg : C.ray.zeroCoefficientPolynomial.natDegree = 1 :=
    C.qs_ray_terminal_degreeOne hthree
  have hidx : e (0 : Fin 4) ∈ C.ray.zeroCoefficientPolynomial.support :=
    C.ray.zeroCoefficientPolynomial_mem_of_face_mem he
  have hle : e (0 : Fin 4) ≤ 1 := by
    rw [← hdeg]
    exact Polynomial.le_natDegree_of_mem_supp _ hidx
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  rcases Nat.eq_zero_or_pos (e (0 : Fin 4)) with he0 | hepos
  · have heq : e = C.ray.facetExponent :=
      C.ray.support_eq_of_zeroCoordinate_eq he C.ray.facet_mem_face
        (he0.trans hfacet0.symm)
    subst e
    exact C.qsOtherFacetSkewWeight_facet_eq_level hthree hne houtThree
  · have he1 : e (0 : Fin 4) = 1 := by omega
    have heq : e = C.ray.outsideExponent :=
      C.ray.support_eq_of_zeroCoordinate_eq he C.ray.outside_mem_face
        (by simpa [he1, hout0])
    subst e
    exact C.qsOtherFacetSkewWeight_outside_eq_level hthree hne houtThree

/-- The skew is genuinely independent from pair degree: on every genuine
other-facet branch it has a nonzero transverse coordinate where pair degree
has coefficient zero. -/
theorem qsOtherFacetSkewWeight_independent_witness
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    ∃ i : Fin 4,
      qsOtherFacetPairWeight next i = 0 ∧
      qsOtherFacetSkewWeight C next i ≠ 0 := by
  cases next
  · have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
    have hout := (mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree
    rcases hbase with ⟨_h0, _h1, _h2, hfacet3⟩
    rcases hout with ⟨_hout1, _hout0, _hout2, hout3⟩
    refine ⟨(2 : Fin 4), by simp [qsOtherFacetPairWeight], ?_⟩
    simp [qsOtherFacetSkewWeight]
    have hf : (0 : ℤ) < C.ray.facetExponent 3 := by exact_mod_cast hfacet3
    have ho : (0 : ℤ) < C.ray.outsideExponent 3 := by exact_mod_cast hout3
    omega
  · have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
    have hout := (mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree
    rcases hbase with ⟨_h0, _h1, hfacet2, _h3⟩
    rcases hout with ⟨_hout3, _hout0, _hout1, hout2⟩
    refine ⟨(1 : Fin 4), by simp [qsOtherFacetPairWeight], ?_⟩
    simp [qsOtherFacetSkewWeight]
    have hf : (0 : ℤ) < C.ray.facetExponent 2 := by exact_mod_cast hfacet2
    have ho : (0 : ℤ) < C.ray.outsideExponent 2 := by exact_mod_cast hout2
    omega
  · exact (hne rfl).elim
  · have hbase := HC4.Newton.mvRankThreeOnFacet_qs hthree
    have hout := (mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree
    rcases hbase with ⟨_h0, _h1, _h2, hfacet3⟩
    rcases hout with ⟨_hout2, _hout0, _hout1, hout3⟩
    refine ⟨(1 : Fin 4), by simp [qsOtherFacetPairWeight], ?_⟩
    simp [qsOtherFacetSkewWeight]
    have hf : (0 : ℤ) < C.ray.facetExponent 3 := by exact_mod_cast hfacet3
    have ho : (0 : ℤ) < C.ray.outsideExponent 3 := by exact_mod_cast hout3
    omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation