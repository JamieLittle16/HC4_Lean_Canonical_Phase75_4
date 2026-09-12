import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarPrimitiveSlice
import HC4.Polynomial.RankThreeQuotientFibers
import Mathlib.Tactic

/-!
# A19 PR quotient fiber of the locked planar direction

On the `.pr` other-facet branch the locked source ray has direction

    (1, -1, -alpha, -beta)

for two strictly positive natural drops `alpha,beta`.  The state-free quotient
coordinates from `RankThreeQuotientFibers` are therefore constant on every
fixed pair-degree planar slice.

This file is only an adapter from the already-verified source-honest line
support to those quotient coordinates.  It introduces no new singularity or
contact argument.
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

/-- Positive transverse drop data for the surviving `.pr` locked ray. -/
structure QsPrLockedQuotientData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) where
  alpha : ℕ
  beta : ℕ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  facet_two_eq : C.ray.facetExponent 2 = C.ray.outsideExponent 2 + alpha
  facet_three_eq : C.ray.facetExponent 3 = C.ray.outsideExponent 3 + beta

/-- The strict coordinatewise direction lock canonically supplies the positive
quotient drops. -/
def qsPrLockedQuotientData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    QsPrLockedQuotientData C := by
  let alpha := C.ray.facetExponent 2 - C.ray.outsideExponent 2
  let beta := C.ray.facetExponent 3 - C.ray.outsideExponent 3
  have hlock := C.qs_ray_pr_outside_strict_directionLock hthree houtThree
  have ha : 0 < alpha := by
    dsimp [alpha]
    omega
  have hb : 0 < beta := by
    dsimp [beta]
    omega
  exact {
    alpha := alpha
    beta := beta
    alpha_pos := ha
    beta_pos := hb
    facet_two_eq := by dsimp [alpha]; omega
    facet_three_eq := by dsimp [beta]; omega
  }

/-- The locked `.pr` direction is literally `(1,-1,-alpha,-beta)` in integer
coordinates. -/
theorem QsPrLockedQuotientData.direction_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (D : QsPrLockedQuotientData C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ((C.ray.outsideExponent 0 : ℤ) - (C.ray.facetExponent 0 : ℤ) = 1) ∧
      ((C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ) = -1) ∧
      ((C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
        -(D.alpha : ℤ)) ∧
      ((C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
        -(D.beta : ℤ)) := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (mvRankThreeOnFacet_qs hthree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have hout1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  have htwoZ :
      (C.ray.facetExponent 2 : ℤ) =
        (C.ray.outsideExponent 2 : ℤ) + (D.alpha : ℤ) := by
    exact_mod_cast D.facet_two_eq
  have hthreeZ :
      (C.ray.facetExponent 3 : ℤ) =
        (C.ray.outsideExponent 3 : ℤ) + (D.beta : ℤ) := by
    exact_mod_cast D.facet_three_eq
  constructor
  · simp [hfacet0, hout0]
  constructor
  · simp [hfacet1, hout1]
  constructor <;> omega

/-- Every pair of points in one actual highest `.pr` slice has the same
rank-three quotient coordinate. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_quotient_eq_of_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (D : QsPrLockedQuotientData C)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ S.slice.support) (hf : f ∈ S.slice.support) :
    rankThreeQuotientCoordinate D.alpha D.beta e =
      rankThreeQuotientCoordinate D.alpha D.beta f := by
  have hpar := S.support_difference_parallel_ray
    hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree he hf
  have hdir := D.direction_eq hthree houtThree
  rcases hdir with ⟨hd0, hd1, hd2, hd3⟩
  have h1 := hpar (1 : Fin 4)
  have h2 := hpar (2 : Fin 4)
  have h3 := hpar (3 : Fin 4)
  rw [hd1] at h1
  rw [hd2] at h2
  rw [hd3] at h3
  rw [rankThreeQuotientCoordinate_eq_iff]
  constructor
  · exact_mod_cast (show
      (e 0 : ℤ) + (e 1 : ℤ) = (f 0 : ℤ) + (f 1 : ℤ) by
        nlinarith [h1])
  constructor
  · exact_mod_cast (show
      (D.alpha : ℤ) * (e 0 : ℤ) + (e 2 : ℤ) =
        (D.alpha : ℤ) * (f 0 : ℤ) + (f 2 : ℤ) by
        nlinarith [h2])
  · exact_mod_cast (show
      (D.beta : ℤ) * (e 0 : ℤ) + (e 3 : ℤ) =
        (D.beta : ℤ) * (f 0 : ℤ) + (f 3 : ℤ) by
        nlinarith [h3])

/-- A nontrivial primitive highest `.pr` slice is therefore an honest
non-singleton quotient fiber. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_primitive_pair_is_quotient_fiber
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial : ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ (D : QsPrLockedQuotientData C)
        (A : QsOtherFacetPlanarAffineRRPackage C .pr P S)
        (e0 e1 : Fin 4 →₀ ℕ),
      S.slice.support = {e0, e1} ∧
      e0 ≠ e1 ∧
      rankThreeQuotientCoordinate D.alpha D.beta e0 =
        rankThreeQuotientCoordinate D.alpha D.beta e1 := by
  let D := C.qsPrLockedQuotientData hthree houtThree
  rcases S.primitive_of_nontrivial hthree
      (by decide : (.pr : ToricFacet) ≠ .qs) houtThree hnontrivial with
    ⟨A, hsupp⟩
  let e0 := A.ray.zeroExponentAt 0
  let e1 := A.ray.zeroExponentAt 1
  have he0 : e0 ∈ S.slice.support := by
    rw [hsupp]
    simp [e0]
  have he1 : e1 ∈ S.slice.support := by
    rw [hsupp]
    simp [e1]
  have hne : e0 ≠ e1 := by
    intro h
    have hset : ({e0, e1} : Finset (Fin 4 →₀ ℕ)) = {e0} := by
      simp [h]
    rw [hsupp, hset] at hnontrivial
    rcases hnontrivial with ⟨a, ha, b, hb, hab⟩
    simp at ha hb
    exact hab (ha.trans hb.symm)
  exact ⟨D, A, e0, e1, hsupp, hne,
    S.pr_quotient_eq_of_mem hthree houtThree D he0 he1⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
