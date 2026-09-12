import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarHighestPairSlice
import Mathlib.Tactic

/-!
# A19 fixed-pair slices are lines parallel to the locked ray

The source-honest planar package retains two affine equations.  On a fixed
pair-degree slice the second neutral wall forces the endpoint-native skew to be
constant.  Together with the exact final source exposure this leaves a
one-dimensional lattice direction.

The only possible degeneracy would be linear dependence of the skew and final
source weight on the two transverse coordinates.  The determinant of those
two rows is, up to sign and a factor two, exactly the positive final Hessian
clock.  Hence it is nonzero.

Consequently any two support exponents of equal pair degree differ by an
integer multiple of the original locked-ray direction.  This is the exact
line-support adapter needed by the state-free line-supported Hessian rigidity
argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

private theorem weight_explicit_fin4
    (a : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight a e =
      a 0 * (e 0 : ℤ) + a 1 * (e 1 : ℤ) +
      a 2 * (e 2 : ℤ) + a 3 * (e 3 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    push_cast
    ring
  · intro i
    simp

private theorem weight_scalar_mul_fin4
    (a : ℤ) (w : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight (fun i => a * w i) e =
      a * Finsupp.weight w e := by
  have h := HC4.Newton.finsupp_weight_fin4_linear_combination
    a w (fun _ => 0) e
  have hz : Finsupp.weight (fun _ : Fin 4 => (0 : ℤ)) e = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype]
    · simp
    · intro i
      simp
  simpa [hz] using h

private theorem weight_wall_combination
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (next : ToricFacet) (a b : ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight
        (fun i =>
          a * qsOtherFacetSkewWeight C next i -
            b * qsOtherFacetPairWeight next i) e =
      a * Finsupp.weight (qsOtherFacetSkewWeight C next) e -
        b * qsOtherFacetPairDegree next e := by
  have h := HC4.Newton.finsupp_weight_fin4_linear_combination
    a (qsOtherFacetSkewWeight C next)
    (fun i => (-b) * qsOtherFacetPairWeight next i) e
  rw [weight_scalar_mul_fin4, finsupp_weight_qsOtherFacetPairWeight] at h
  simpa [sub_eq_add_neg, neg_mul] using h

/-- Every support point of the final source carrier attains the exact final
source level. -/
theorem QsOtherFacetPlanarCarrierPackage.support_final_level
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    Finsupp.weight P.finalWeight e = P.finalLevel := by
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  have hface := HC4.Newton.initialForm_support_isExposedFace
    P.finalWeight P.finalLevel F P.source_bound
  have hEq := P.carrier_eq_initialForm
  rw [← hEq] at hface
  exact hface.weight_eq (by simpa using he)

/-- On one fixed pair-degree slice, the endpoint-native skew is constant. -/
theorem QsOtherFacetPlanarCarrierPackage.skew_eq_of_pairDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair : qsOtherFacetPairDegree next e =
      qsOtherFacetPairDegree next f) :
    Finsupp.weight (qsOtherFacetSkewWeight C next) e =
      Finsupp.weight (qsOtherFacetSkewWeight C next) f := by
  have heWall := P.support_wall_level he
  have hfWall := P.support_wall_level hf
  rw [P.wallWeight_eq] at heWall hfWall
  simp only [weight_wall_combination] at heWall hfWall
  have hmul :
      P.pairGap *
        (Finsupp.weight (qsOtherFacetSkewWeight C next) e -
          Finsupp.weight (qsOtherFacetSkewWeight C next) f) = 0 := by
    nlinarith
  have hgap0 : P.pairGap ≠ 0 := ne_of_gt P.pairGap_pos
  have hdiff := (mul_eq_zero.mp hmul).resolve_left hgap0
  exact sub_eq_zero.mp hdiff

private theorem two_by_two_kernel_zero
    {a b c d x y : ℤ}
    (hdet : a * d - b * c ≠ 0)
    (h₁ : a * x + b * y = 0)
    (h₂ : c * x + d * y = 0) :
    x = 0 ∧ y = 0 := by
  have hx : (a * d - b * c) * x = 0 := by
    linear_combination d * h₁ - b * h₂
  have hy : (a * d - b * c) * y = 0 := by
    linear_combination a * h₂ - c * h₁
  exact ⟨(mul_eq_zero.mp hx).resolve_left hdet,
    (mul_eq_zero.mp hy).resolve_left hdet⟩

private theorem pr_transverseDet_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    qsOtherFacetSkewWeight C .pr 2 * P.finalWeight 3 -
      qsOtherFacetSkewWeight C .pr 3 * P.finalWeight 2 ≠ 0 := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hout1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  have hfacetMem : C.ray.facetExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.facet_mem_face)
    simpa using h
  have houtMem : C.ray.outsideExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.outside_mem_face)
    simpa using h
  have hfacetLevel := P.support_final_level hfacetMem
  have houtLevel := P.support_final_level houtMem
  simp only [weight_explicit_fin4] at hfacetLevel houtLevel
  simp [hfacet0, hfacet1, hout0, hout1] at hfacetLevel houtLevel
  have hclock := P.hessianClock_pos
  rw [Fin.sum_univ_four] at hclock
  intro hdet
  simp [qsOtherFacetSkewWeight] at hdet
  nlinarith

private theorem sp_transverseDet_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .sp)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    qsOtherFacetSkewWeight C .sp 1 * P.finalWeight 3 -
      qsOtherFacetSkewWeight C .sp 3 * P.finalWeight 1 ≠ 0 := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  have hfacet2 : C.ray.facetExponent (2 : Fin 4) = 1 :=
    (C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hout2 : C.ray.outsideExponent (2 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree).1
  have hfacetMem : C.ray.facetExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.facet_mem_face)
    simpa using h
  have houtMem : C.ray.outsideExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.outside_mem_face)
    simpa using h
  have hfacetLevel := P.support_final_level hfacetMem
  have houtLevel := P.support_final_level houtMem
  simp only [weight_explicit_fin4] at hfacetLevel houtLevel
  simp [hfacet0, hfacet2, hout0, hout2] at hfacetLevel houtLevel
  have hclock := P.hessianClock_pos
  rw [Fin.sum_univ_four] at hclock
  intro hdet
  simp [qsOtherFacetSkewWeight] at hdet
  nlinarith

private theorem rq_transverseDet_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .rq)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    qsOtherFacetSkewWeight C .rq 1 * P.finalWeight 2 -
      qsOtherFacetSkewWeight C .rq 2 * P.finalWeight 1 ≠ 0 := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
  have hfacet3 : C.ray.facetExponent (3 : Fin 4) = 1 :=
    (C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hout3 : C.ray.outsideExponent (3 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree).1
  have hfacetMem : C.ray.facetExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.facet_mem_face)
    simpa using h
  have houtMem : C.ray.outsideExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.outside_mem_face)
    simpa using h
  have hfacetLevel := P.support_final_level hfacetMem
  have houtLevel := P.support_final_level houtMem
  simp only [weight_explicit_fin4] at hfacetLevel houtLevel
  simp [hfacet0, hfacet3, hout0, hout3] at hfacetLevel houtLevel
  have hclock := P.hessianClock_pos
  rw [Fin.sum_univ_four] at hclock
  intro hdet
  simp [qsOtherFacetSkewWeight] at hdet
  nlinarith

/-- **Fixed pair-degree line support.**  Two points of the source-honest planar
carrier with the same pair degree differ by the corresponding integer multiple
of the original locked-ray endpoint direction. -/
theorem QsOtherFacetPlanarCarrierPackage.support_difference_parallel_ray
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair : qsOtherFacetPairDegree next e =
      qsOtherFacetPairDegree next f) :
    ∀ i : Fin 4,
      (e i : ℤ) - (f i : ℤ) =
        ((e 0 : ℤ) - (f 0 : ℤ)) *
          ((C.ray.outsideExponent i : ℤ) -
            (C.ray.facetExponent i : ℤ)) := by
  have hskew := P.skew_eq_of_pairDegree_eq he hf hpair
  have hfinalE := P.support_final_level he
  have hfinalF := P.support_final_level hf
  have hfinal : Finsupp.weight P.finalWeight e =
      Finsupp.weight P.finalWeight f := hfinalE.trans hfinalF.symm
  have hfacetSkew := C.qsOtherFacetSkewWeight_facet_eq_level
    hthree hne houtThree
  have houtSkew := C.qsOtherFacetSkewWeight_outside_eq_level
    hthree hne houtThree
  have hskewRay :
      Finsupp.weight (qsOtherFacetSkewWeight C next) C.ray.outsideExponent =
        Finsupp.weight (qsOtherFacetSkewWeight C next) C.ray.facetExponent :=
    houtSkew.trans hfacetSkew.symm
  have hfacetMem : C.ray.facetExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.facet_mem_face)
    simpa using h
  have houtMem : C.ray.outsideExponent ∈ P.carrier.support := by
    have h := P.ray_support_subset (by simpa using C.ray.outside_mem_face)
    simpa using h
  have hfacetFinal := P.support_final_level hfacetMem
  have houtFinal := P.support_final_level houtMem
  have hfinalRay :
      Finsupp.weight P.finalWeight C.ray.outsideExponent =
        Finsupp.weight P.finalWeight C.ray.facetExponent :=
    houtFinal.trans hfacetFinal.symm

  fin_cases next
  · exact (hne rfl).elim
  · have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
      (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
    have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
      (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
    have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
      C.qs_ray_outside_zeroCoordinate_eq_one hthree
    have hout1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
      ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
    have hdet := pr_transverseDet_ne_zero C P hthree houtThree
    simp [qsOtherFacetPairDegree] at hpair
    simp only [weight_explicit_fin4] at hskew hfinal hskewRay hfinalRay
    simp [qsOtherFacetSkewWeight, hfacet0, hfacet1, hout0, hout1] at hskew hskewRay
    simp [hfacet0, hfacet1, hout0, hout1] at hfinalRay
    let t : ℤ := (e 0 : ℤ) - (f 0 : ℤ)
    let r2 : ℤ :=
      (e 2 : ℤ) - (f 2 : ℤ) -
        t * ((C.ray.outsideExponent 2 : ℤ) -
          (C.ray.facetExponent 2 : ℤ))
    let r3 : ℤ :=
      (e 3 : ℤ) - (f 3 : ℤ) -
        t * ((C.ray.outsideExponent 3 : ℤ) -
          (C.ray.facetExponent 3 : ℤ))
    have hsr :
        qsOtherFacetSkewWeight C .pr 2 * r2 +
          qsOtherFacetSkewWeight C .pr 3 * r3 = 0 := by
      dsimp [r2, r3, t]
      nlinarith
    have hwr : P.finalWeight 2 * r2 + P.finalWeight 3 * r3 = 0 := by
      dsimp [r2, r3, t]
      nlinarith
    have hr := two_by_two_kernel_zero hdet hsr hwr
    intro i
    fin_cases i
    · simp [t, hfacet0, hout0]
    · dsimp [t]
      simp [hfacet1, hout1]
      linarith
    · dsimp [r2, t] at hr
      exact sub_eq_zero.mp hr.1
    · dsimp [r3, t] at hr
      exact sub_eq_zero.mp hr.2
  · have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
      (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
    have hfacet2 : C.ray.facetExponent (2 : Fin 4) = 1 :=
      (C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree).1
    have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
      C.qs_ray_outside_zeroCoordinate_eq_one hthree
    have hout2 : C.ray.outsideExponent (2 : Fin 4) = 0 :=
      ((mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree).1
    have hdet := sp_transverseDet_ne_zero C P hthree houtThree
    simp [qsOtherFacetPairDegree] at hpair
    simp only [weight_explicit_fin4] at hskew hfinal hskewRay hfinalRay
    simp [qsOtherFacetSkewWeight, hfacet0, hfacet2, hout0, hout2] at hskew hskewRay
    simp [hfacet0, hfacet2, hout0, hout2] at hfinalRay
    let t : ℤ := (e 0 : ℤ) - (f 0 : ℤ)
    let r1 : ℤ :=
      (e 1 : ℤ) - (f 1 : ℤ) -
        t * ((C.ray.outsideExponent 1 : ℤ) -
          (C.ray.facetExponent 1 : ℤ))
    let r3 : ℤ :=
      (e 3 : ℤ) - (f 3 : ℤ) -
        t * ((C.ray.outsideExponent 3 : ℤ) -
          (C.ray.facetExponent 3 : ℤ))
    have hsr :
        qsOtherFacetSkewWeight C .sp 1 * r1 +
          qsOtherFacetSkewWeight C .sp 3 * r3 = 0 := by
      dsimp [r1, r3, t]
      nlinarith
    have hwr : P.finalWeight 1 * r1 + P.finalWeight 3 * r3 = 0 := by
      dsimp [r1, r3, t]
      nlinarith
    have hr := two_by_two_kernel_zero hdet hsr hwr
    intro i
    fin_cases i
    · simp [t, hfacet0, hout0]
    · dsimp [r1, t] at hr
      exact sub_eq_zero.mp hr.1
    · dsimp [t]
      simp [hfacet2, hout2]
      linarith
    · dsimp [r3, t] at hr
      exact sub_eq_zero.mp hr.2
  · have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
      (HC4.Newton.mvRankThreeOnFacet_qs hthree).1
    have hfacet3 : C.ray.facetExponent (3 : Fin 4) = 1 :=
      (C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree).1
    have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
      C.qs_ray_outside_zeroCoordinate_eq_one hthree
    have hout3 : C.ray.outsideExponent (3 : Fin 4) = 0 :=
      ((mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree).1
    have hdet := rq_transverseDet_ne_zero C P hthree houtThree
    simp [qsOtherFacetPairDegree] at hpair
    simp only [weight_explicit_fin4] at hskew hfinal hskewRay hfinalRay
    simp [qsOtherFacetSkewWeight, hfacet0, hfacet3, hout0, hout3] at hskew hskewRay
    simp [hfacet0, hfacet3, hout0, hout3] at hfinalRay
    let t : ℤ := (e 0 : ℤ) - (f 0 : ℤ)
    let r1 : ℤ :=
      (e 1 : ℤ) - (f 1 : ℤ) -
        t * ((C.ray.outsideExponent 1 : ℤ) -
          (C.ray.facetExponent 1 : ℤ))
    let r2 : ℤ :=
      (e 2 : ℤ) - (f 2 : ℤ) -
        t * ((C.ray.outsideExponent 2 : ℤ) -
          (C.ray.facetExponent 2 : ℤ))
    have hsr :
        qsOtherFacetSkewWeight C .rq 1 * r1 +
          qsOtherFacetSkewWeight C .rq 2 * r2 = 0 := by
      dsimp [r1, r2, t]
      nlinarith
    have hwr : P.finalWeight 1 * r1 + P.finalWeight 2 * r2 = 0 := by
      dsimp [r1, r2, t]
      nlinarith
    have hr := two_by_two_kernel_zero hdet hsr hwr
    intro i
    fin_cases i
    · simp [t, hfacet0, hout0]
    · dsimp [r1, t] at hr
      exact sub_eq_zero.mp hr.1
    · dsimp [r2, t] at hr
      exact sub_eq_zero.mp hr.2
    · dsimp [t]
      simp [hfacet3, hout3]
      linarith

/-- The actual highest pair slice inherits the same affine line direction. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.support_difference_parallel_ray
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ S.slice.support) (hf : f ∈ S.slice.support) :
    ∀ i : Fin 4,
      (e i : ℤ) - (f i : ℤ) =
        ((e 0 : ℤ) - (f 0 : ℤ)) *
          ((C.ray.outsideExponent i : ℤ) -
            (C.ray.facetExponent i : ℤ)) := by
  have heData := S.support_parent_and_pairLevel he
  have hfData := S.support_parent_and_pairLevel hf
  exact P.support_difference_parallel_ray hthree hne houtThree
    heData.1 hfData.1 (heData.2.trans hfData.2.symm)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
