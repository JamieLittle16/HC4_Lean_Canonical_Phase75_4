import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedQuotientFibers
import HC4.Polynomial.RankThreeQuotientWeightFactorization
import Mathlib.Tactic

/-!
# A19 planar equations on normalized PR quotient space

The source-honest planar carrier stores two affine support equations.  Once the
locked direction has been normalized, both weights annihilate that primitive
direction because the two original locked-ray endpoints lie in the carrier at
the same two levels.

Therefore both equations factor through rank-three quotient coordinates.  The
quotient image of the entire carrier lies on the intersection of two affine
hyperplanes in the three-dimensional quotient lattice, i.e. on an affine
quotient line.  This is the structural input needed for the final
singleton/no-singleton reconstruction.
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

private theorem ray_endpoints_mem_planarCarrier
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr} :
    C.ray.facetExponent ∈ P.carrier.support ∧
      C.ray.outsideExponent ∈ P.carrier.support := by
  constructor
  · have h := P.ray_support_subset
      (show C.ray.facetExponent ∈ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) by
        simpa using C.ray.facet_mem_face)
    simpa using h
  · have h := P.ray_support_subset
      (show C.ray.outsideExponent ∈ (↑C.ray.face.support : Set (Fin 4 →₀ ℕ)) by
        simpa using C.ray.outside_mem_face)
    simpa using h

private theorem normalized_left_primitive_pair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1)
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
        -(V : ℤ)) :
    C.ray.outsideExponent 0 = C.ray.facetExponent 0 + 1 ∧
      C.ray.facetExponent 1 = C.ray.outsideExponent 1 + 1 ∧
      C.ray.facetExponent 2 = C.ray.outsideExponent 2 + 1 ∧
      C.ray.facetExponent 3 = C.ray.outsideExponent 3 + V := by
  have hf0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (mvRankThreeOnFacet_qs hthree).1
  have ho0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hf1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have ho1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  refine ⟨by omega, by omega, ?_, ?_⟩
  · exact_mod_cast (show
      (C.ray.facetExponent 2 : ℤ) =
        (C.ray.outsideExponent 2 : ℤ) + 1 by omega)
  · exact_mod_cast (show
      (C.ray.facetExponent 3 : ℤ) =
        (C.ray.outsideExponent 3 : ℤ) + (V : ℤ) by omega)

private theorem normalized_right_primitive_pair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
        -(V : ℤ))
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1) :
    C.ray.outsideExponent 0 = C.ray.facetExponent 0 + 1 ∧
      C.ray.facetExponent 1 = C.ray.outsideExponent 1 + 1 ∧
      C.ray.facetExponent 2 = C.ray.outsideExponent 2 + V ∧
      C.ray.facetExponent 3 = C.ray.outsideExponent 3 + 1 := by
  have hf0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (mvRankThreeOnFacet_qs hthree).1
  have ho0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hf1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have ho1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  refine ⟨by omega, by omega, ?_, ?_⟩
  · exact_mod_cast (show
      (C.ray.facetExponent 2 : ℤ) =
        (C.ray.outsideExponent 2 : ℤ) + (V : ℤ) by omega)
  · exact_mod_cast (show
      (C.ray.facetExponent 3 : ℤ) =
        (C.ray.outsideExponent 3 : ℤ) + 1 by omega)

/-- In the left primitive orientation, both retained planar weights factor
through quotient coordinates `(1,V)`. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_normalized_left_weights_neutral
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1)
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
        -(V : ℤ)) :
    RankThreeDirectionNeutralWeight 1 V P.firstWeight ∧
      RankThreeDirectionNeutralWeight 1 V P.wallWeight := by
  rcases normalized_left_primitive_pair hthree houtThree hdir2 hdir3 with
    ⟨h0, h1, h2, h3⟩
  rcases ray_endpoints_mem_planarCarrier (C := C) (P := P) with ⟨hf, ho⟩
  have hwFirst :
      Finsupp.weight P.firstWeight C.ray.facetExponent =
        Finsupp.weight P.firstWeight C.ray.outsideExponent := by
    rw [P.support_first_level hf, P.support_first_level ho]
  have hwWall :
      Finsupp.weight P.wallWeight C.ray.facetExponent =
        Finsupp.weight P.wallWeight C.ray.outsideExponent := by
    rw [P.support_wall_level hf, P.support_wall_level ho]
  exact ⟨
    rankThreeDirectionNeutralWeight_of_primitive_pair 1 V P.firstWeight
      C.ray.facetExponent C.ray.outsideExponent h0 h1 h2 h3 hwFirst,
    rankThreeDirectionNeutralWeight_of_primitive_pair 1 V P.wallWeight
      C.ray.facetExponent C.ray.outsideExponent h0 h1 h2 h3 hwWall⟩

/-- Symmetric neutral-weight statement for the `(V,1)` orientation. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_normalized_right_weights_neutral
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
        -(V : ℤ))
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1) :
    RankThreeDirectionNeutralWeight V 1 P.firstWeight ∧
      RankThreeDirectionNeutralWeight V 1 P.wallWeight := by
  rcases normalized_right_primitive_pair hthree houtThree hdir2 hdir3 with
    ⟨h0, h1, h2, h3⟩
  rcases ray_endpoints_mem_planarCarrier (C := C) (P := P) with ⟨hf, ho⟩
  have hwFirst :
      Finsupp.weight P.firstWeight C.ray.facetExponent =
        Finsupp.weight P.firstWeight C.ray.outsideExponent := by
    rw [P.support_first_level hf, P.support_first_level ho]
  have hwWall :
      Finsupp.weight P.wallWeight C.ray.facetExponent =
        Finsupp.weight P.wallWeight C.ray.outsideExponent := by
    rw [P.support_wall_level hf, P.support_wall_level ho]
  exact ⟨
    rankThreeDirectionNeutralWeight_of_primitive_pair V 1 P.firstWeight
      C.ray.facetExponent C.ray.outsideExponent h0 h1 h2 h3 hwFirst,
    rankThreeDirectionNeutralWeight_of_primitive_pair V 1 P.wallWeight
      C.ray.facetExponent C.ray.outsideExponent h0 h1 h2 h3 hwWall⟩

/-- Every actual carrier support exponent maps onto the two retained quotient
hyperplanes in the left orientation. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_normalized_left_quotient_line
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1)
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
        -(V : ℤ))
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    rankThreeQuotientWeight P.firstWeight
        (rankThreeQuotientCoordinate 1 V e) = P.firstLevel ∧
      rankThreeQuotientWeight P.wallWeight
        (rankThreeQuotientCoordinate 1 V e) = P.wallLevel := by
  rcases P.pr_normalized_left_weights_neutral
      hthree houtThree hdir2 hdir3 with ⟨hfirst, hwall⟩
  constructor
  · rw [← finsupp_weight_eq_rankThreeQuotientWeight 1 V P.firstWeight hfirst e]
    exact P.support_first_level he
  · rw [← finsupp_weight_eq_rankThreeQuotientWeight 1 V P.wallWeight hwall e]
    exact P.support_wall_level he

/-- Symmetric quotient-line statement in the `(V,1)` orientation. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_normalized_right_quotient_line
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
        -(V : ℤ))
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    rankThreeQuotientWeight P.firstWeight
        (rankThreeQuotientCoordinate V 1 e) = P.firstLevel ∧
      rankThreeQuotientWeight P.wallWeight
        (rankThreeQuotientCoordinate V 1 e) = P.wallLevel := by
  rcases P.pr_normalized_right_weights_neutral
      hthree houtThree hdir2 hdir3 with ⟨hfirst, hwall⟩
  constructor
  · rw [← finsupp_weight_eq_rankThreeQuotientWeight V 1 P.firstWeight hfirst e]
    exact P.support_first_level he
  · rw [← finsupp_weight_eq_rankThreeQuotientWeight V 1 P.wallWeight hwall e]
    exact P.support_wall_level he

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
