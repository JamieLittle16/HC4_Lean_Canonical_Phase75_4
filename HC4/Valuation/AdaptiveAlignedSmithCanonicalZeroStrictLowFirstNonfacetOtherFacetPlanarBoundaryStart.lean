import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarLineSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetDirectionLock
import HC4.Newton.InteriorVertex
import HC4.RationalRigidity.LineSupportedHessianRigidity
import Mathlib.Tactic

/-!
# A19 boundary start for the source-honest highest planar slice

The highest pair slice is already Lean-verified to be Hessian-singular and to
lie on the affine line parallel to the original locked source ray.  To feed it
to the state-free rank-three line rigidity theorem we must orient that affine
line honestly: its first occupied point in the omitted coordinate must start
on the coordinate boundary.

This file isolates the elementary lattice part of that normalization.  At an
other-facet rank-three endpoint, coordinate `0` increases from `0` to `1` and
every transverse coordinate decreases strictly.  Hence coordinate `0` is an
injective parameter on the highest slice.  Any support point minimal in that
coordinate has all three transverse coordinates strictly positive as soon as
the slice contains a second monomial.  Exposing that point by the weight
`(-1,0,0,0)` and using singularity then forces the only remaining possible
boundary coordinate, namely coordinate `0`, to vanish.

No new Hessian calculation, balance relation, repair tag, or JC2 assumption is
introduced.
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

/-- The locked source ray has positive unit motion in coordinate `0` and
strictly negative motion in every transverse coordinate.  This packages the
three cyclic `.pr/.sp/.rq` direction-lock theorems behind one interface. -/
theorem qs_ray_otherFacet_locked_direction_signs
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet} (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent) :
    C.ray.facetExponent 0 = 0 ∧
      C.ray.outsideExponent 0 = 1 ∧
      ∀ i : Fin 4, i ≠ 0 →
        C.ray.outsideExponent i < C.ray.facetExponent i := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (mvRankThreeOnFacet_qs hthree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  refine ⟨hfacet0, hout0, ?_⟩
  cases next with
  | qs => exact (hne rfl).elim
  | pr =>
      have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
        (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
      have hout1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
        ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
      have hlock := C.qs_ray_pr_outside_strict_directionLock hthree houtThree
      intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · simp [hfacet1, hout1]
      · exact hlock.2.1
      · exact hlock.2.2
  | sp =>
      have hfacet2 : C.ray.facetExponent (2 : Fin 4) = 1 :=
        (C.qs_ray_sp_outside_base_eq_one_and_cross hthree houtThree).1
      have hout2 : C.ray.outsideExponent (2 : Fin 4) = 0 :=
        ((mvRankThreeOnFacet_iff .sp C.ray.outsideExponent).1 houtThree).1
      have hlock := C.qs_ray_sp_outside_strict_directionLock hthree houtThree
      intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact hlock.2.1
      · simp [hfacet2, hout2]
      · exact hlock.2.2
  | rq =>
      have hfacet3 : C.ray.facetExponent (3 : Fin 4) = 1 :=
        (C.qs_ray_rq_outside_base_eq_one_and_cross hthree houtThree).1
      have hout3 : C.ray.outsideExponent (3 : Fin 4) = 0 :=
        ((mvRankThreeOnFacet_iff .rq C.ray.outsideExponent).1 houtThree).1
      have hlock := C.qs_ray_rq_outside_strict_directionLock hthree houtThree
      intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact hlock.2.1
      · exact hlock.2.2
      · simp [hfacet3, hout3]

/-- Coordinate `0` is an injective lattice parameter on an actual highest
pair slice. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.eq_of_zeroCoordinate_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ S.slice.support) (hf : f ∈ S.slice.support)
    (hzero : e 0 = f 0) : e = f := by
  have hpar := S.support_difference_parallel_ray hthree hne houtThree he hf
  ext i
  have hi := hpar i
  have ht : (e 0 : ℤ) - (f 0 : ℤ) = 0 := by
    exact_mod_cast sub_eq_zero.mpr hzero
  rw [ht] at hi
  simp only [zero_mul] at hi
  have hiz : (e i : ℤ) = (f i : ℤ) := sub_eq_zero.mp hi
  exact_mod_cast hiz

/-- A minimal-`x₀` support point of a nontrivial highest slice has all three
transverse coordinates strictly positive. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.minimal_zeroCoordinate_transverse_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    {P : QsOtherFacetPlanarCarrierPackage C next}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C next P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (hne : next ≠ .qs)
    (houtThree : MvRankThreeOnFacet next C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ}
    (he : e ∈ S.slice.support)
    (hmin : ∀ d ∈ S.slice.support, e 0 ≤ d 0)
    (hother : ∃ f ∈ S.slice.support, f ≠ e) :
    ∀ i : Fin 4, i ≠ 0 → 0 < e i := by
  rcases hother with ⟨f, hf, hfe⟩
  have hef0 : e 0 < f 0 := by
    have hle := hmin f hf
    have hne0 : e 0 ≠ f 0 := by
      intro hEq
      exact hfe (S.eq_of_zeroCoordinate_eq hthree hne houtThree hf he hEq.symm)
    omega
  have hsigns := C.qs_ray_otherFacet_locked_direction_signs hthree hne houtThree
  have hpar := S.support_difference_parallel_ray hthree hne houtThree he hf
  intro i hi
  have hstepNat : C.ray.outsideExponent i < C.ray.facetExponent i :=
    hsigns.2.2 i hi
  have htneg : (e 0 : ℤ) - (f 0 : ℤ) < 0 := by
    exact_mod_cast hef0
  have hstepneg :
      (C.ray.outsideExponent i : ℤ) -
          (C.ray.facetExponent i : ℤ) < 0 := by
    exact_mod_cast hstepNat
  have hprod :
      0 < ((e 0 : ℤ) - (f 0 : ℤ)) *
        ((C.ray.outsideExponent i : ℤ) -
          (C.ray.facetExponent i : ℤ)) :=
    mul_pos_of_neg_of_neg htneg hstepneg
  have hiEq := hpar i
  have hfiNonneg : (0 : ℤ) ≤ (f i : ℤ) := by positivity
  have heiPos : (0 : ℤ) < (e i : ℤ) := by
    nlinarith
  exact_mod_cast heiPos

private def negativeZeroCoordinateWeight : Fin 4 → ℤ :=
  fun i => if i = 0 then -1 else 0

private theorem finsupp_weight_negativeZeroCoordinateWeight
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight negativeZeroCoordinateWeight d = -(d 0 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    simp [negativeZeroCoordinateWeight]
  · intro i
    simp

/-- **Boundary-start normalization for a nontrivial highest slice.**

If the highest pair slice contains two distinct monomials, then its
minimal-`x₀` support point is a genuine `.qs` boundary point: coordinate `0`
is zero while all three transverse coordinates are positive. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.exists_boundary_start_of_nontrivial
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
    ∃ e ∈ S.slice.support,
      e 0 = 0 ∧ ∀ i : Fin 4, i ≠ 0 → 0 < e i := by
  have hsupp : S.slice.support.Nonempty :=
    MvPolynomial.support_nonempty.mpr S.slice_ne_zero
  let levels : Finset ℕ := S.slice.support.image (fun d => d (0 : Fin 4))
  have hlevels : levels.Nonempty := by
    dsimp [levels]
    exact hsupp.image _
  let m : ℕ := levels.min' hlevels
  have hm : m ∈ levels := by
    dsimp [m]
    exact Finset.min'_mem levels hlevels
  have hm' : m ∈ S.slice.support.image (fun d => d (0 : Fin 4)) := by
    simpa [levels] using hm
  rcases Finset.mem_image.mp hm' with ⟨e, he, heq⟩
  have hmin : ∀ d ∈ S.slice.support, e 0 ≤ d 0 := by
    intro d hd
    have hdlevel : d 0 ∈ levels := by
      dsimp [levels]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hle : m ≤ d 0 := Finset.min'_le levels (d 0) hdlevel
    omega
  rcases hnontrivial with ⟨a, ha, b, hb, hab⟩
  have hother : ∃ f ∈ S.slice.support, f ≠ e := by
    by_cases hae : a = e
    · refine ⟨b, hb, ?_⟩
      intro hbe
      exact hab (hae.trans hbe.symm)
    · exact ⟨a, ha, hae⟩
  have htrans := S.minimal_zeroCoordinate_transverse_pos
    hthree hne houtThree he hmin hother
  have h1 : 0 < e (1 : Fin 4) := htrans 1 (by decide)
  have h2 : 0 < e (2 : Fin 4) := htrans 2 (by decide)
  have h3 : 0 < e (3 : Fin 4) := htrans 3 (by decide)
  have hdeg : 3 ≤ ordinaryDegree4 e := by
    simp only [ordinaryDegree4]
    omega
  let level : ℤ := -(e 0 : ℤ)
  have hbound : IsWeightLE negativeZeroCoordinateWeight level S.slice := by
    intro d hd
    rw [finsupp_weight_negativeZeroCoordinateWeight]
    dsimp [level]
    have hle := hmin d hd
    have hleZ : (e 0 : ℤ) ≤ (d 0 : ℤ) := by exact_mod_cast hle
    omega
  have heWeight :
      Finsupp.weight negativeZeroCoordinateWeight e = level := by
    rw [finsupp_weight_negativeZeroCoordinateWeight]
  have hinit :
      initialForm negativeZeroCoordinateWeight level S.slice =
        MvPolynomial.monomial e (MvPolynomial.coeff e S.slice) := by
    ext d
    rw [coeff_initialForm]
    by_cases hdWeight :
        Finsupp.weight negativeZeroCoordinateWeight d = level
    · rw [if_pos hdWeight]
      by_cases hde : d = e
      · subst d
        simp
      · have hd0 : d 0 = e 0 := by
          rw [finsupp_weight_negativeZeroCoordinateWeight] at hdWeight
          dsimp [level] at hdWeight
          have hz : (d 0 : ℤ) = (e 0 : ℤ) := by omega
          exact_mod_cast hz
        have hcoeffZero : MvPolynomial.coeff d S.slice = 0 := by
          by_contra hcoeff
          have hdmem : d ∈ S.slice.support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          exact hde (S.eq_of_zeroCoordinate_eq
            hthree hne houtThree hdmem he hd0)
        simp [hcoeffZero, hde]
    · rw [if_neg hdWeight]
      have hde : d ≠ e := by
        intro hde
        subst d
        exact hdWeight heWeight
      simp [hde]
  have hc : MvPolynomial.coeff e S.slice ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  have hboundary := HC4.Newton.exposed_monomial_on_boundary_of_zero_hessian
    hbound S.hessian_zero hinit hc hdeg
  have hzero := (mvExponentOnBoundary_iff_coordinate_zero e).1 hboundary
  have he0 : e 0 = 0 := by
    rcases hzero with h0 | h1z | h2z | h3z
    · exact h0
    · exact (Nat.ne_of_gt h1 h1z).elim
    · exact (Nat.ne_of_gt h2 h2z).elim
    · exact (Nat.ne_of_gt h3 h3z).elim
  exact ⟨e, he, he0, htrans⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
