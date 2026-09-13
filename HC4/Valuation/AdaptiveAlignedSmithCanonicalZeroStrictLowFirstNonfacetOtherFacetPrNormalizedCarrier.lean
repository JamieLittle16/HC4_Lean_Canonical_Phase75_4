import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedQuotientLine
import Mathlib.Tactic

/-!
# A19 normalized PR planar-carrier frontier

The primitive highest pair slice normalizes the locked `.pr` source direction,
while the planar carrier retains two exact affine source equations.  This file
packages those facts for the *whole* carrier in the form needed by the final
contact-aware reconstruction.

For quotient drops `(alpha,beta)` we retain simultaneously:

* the literal locked source direction `(1,-1,-alpha,-beta)`;
* neutrality of both retained planar weights along that direction;
* both affine equations on every actual carrier support exponent, after
  factorization to rank-three quotient coordinates; and
* the fact that every fixed pair-degree carrier slice is one quotient fiber.

The nontrivial highest slice then gives the exact exhaustive frontier

* `(alpha,beta)=(1,1)`, or
* `(alpha,beta)=(1,V)` with `V>1`, or
* `(alpha,beta)=(V,1)` with `V>1`.

No contact clock is identified with the ray or blocker clock, and no new
singularity statement is introduced here.
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

/-- Source-honest quotient geometry of the whole planar carrier after the
locked `.pr` direction has been normalized. -/
structure QsOtherFacetPrQuotientCarrierData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (alpha beta : ℕ) where
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  direction_zero :
    (C.ray.outsideExponent 0 : ℤ) - (C.ray.facetExponent 0 : ℤ) = 1
  direction_one :
    (C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ) = -1
  direction_two :
    (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
      -(alpha : ℤ)
  direction_three :
    (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
      -(beta : ℤ)
  firstWeight_neutral :
    RankThreeDirectionNeutralWeight alpha beta P.firstWeight
  wallWeight_neutral :
    RankThreeDirectionNeutralWeight alpha beta P.wallWeight
  support_quotient_line :
    ∀ {e : Fin 4 →₀ ℕ}, e ∈ P.carrier.support →
      rankThreeQuotientWeight P.firstWeight
          (rankThreeQuotientCoordinate alpha beta e) = P.firstLevel ∧
        rankThreeQuotientWeight P.wallWeight
          (rankThreeQuotientCoordinate alpha beta e) = P.wallLevel
  pair_fiber :
    ∀ {e f : Fin 4 →₀ ℕ},
      e ∈ P.carrier.support → f ∈ P.carrier.support →
      qsOtherFacetPairDegree .pr e = qsOtherFacetPairDegree .pr f →
      rankThreeQuotientCoordinate alpha beta e =
        rankThreeQuotientCoordinate alpha beta f

/-- Package the whole carrier in the normalized left orientation
`(1,-1,-1,-V)`. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_leftQuotientCarrierData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ} (hV : 0 < V)
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1)
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
        -(V : ℤ)) :
    Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 V) := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (mvRankThreeOnFacet_qs hthree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have hout1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  rcases P.pr_normalized_left_weights_neutral
      hthree houtThree hdir2 hdir3 with ⟨hfirst, hwall⟩
  exact ⟨{
    alpha_pos := by norm_num
    beta_pos := hV
    direction_zero := by simp [hfacet0, hout0]
    direction_one := by simp [hfacet1, hout1]
    direction_two := by simpa using hdir2
    direction_three := hdir3
    firstWeight_neutral := hfirst
    wallWeight_neutral := hwall
    support_quotient_line := by
      intro e he
      exact P.pr_normalized_left_quotient_line
        hthree houtThree hdir2 hdir3 he
    pair_fiber := by
      intro e f he hf hpair
      exact P.pr_quotient_eq_of_normalized_left
        hthree houtThree hdir2 hdir3 he hf hpair
  }⟩

/-- Package the whole carrier in the normalized right orientation
`(1,-1,-V,-1)`. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_rightQuotientCarrierData
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ} (hV : 0 < V)
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
        -(V : ℤ))
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1) :
    Nonempty (QsOtherFacetPrQuotientCarrierData C P V 1) := by
  have hfacet0 : C.ray.facetExponent (0 : Fin 4) = 0 :=
    (mvRankThreeOnFacet_qs hthree).1
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  have hfacet1 : C.ray.facetExponent (1 : Fin 4) = 1 :=
    (C.qs_ray_pr_outside_base_eq_one_and_cross hthree houtThree).1
  have hout1 : C.ray.outsideExponent (1 : Fin 4) = 0 :=
    ((mvRankThreeOnFacet_iff .pr C.ray.outsideExponent).1 houtThree).1
  rcases P.pr_normalized_right_weights_neutral
      hthree houtThree hdir2 hdir3 with ⟨hfirst, hwall⟩
  exact ⟨{
    alpha_pos := hV
    beta_pos := by norm_num
    direction_zero := by simp [hfacet0, hout0]
    direction_one := by simp [hfacet1, hout1]
    direction_two := hdir2
    direction_three := by simpa using hdir3
    firstWeight_neutral := hfirst
    wallWeight_neutral := hwall
    support_quotient_line := by
      intro e he
      exact P.pr_normalized_right_quotient_line
        hthree houtThree hdir2 hdir3 he
    pair_fiber := by
      intro e f he hf hpair
      exact P.pr_quotient_eq_of_normalized_right
        hthree houtThree hdir2 hdir3 he hf hpair
  }⟩

/-- **Normalized PR carrier frontier.**  A nontrivial source-honest highest
slice puts the entire planar carrier into exactly the unit, left `V>1`, or
right `V>1` quotient geometry.  This is the input expected by the remaining
contact-aware singleton/two-function reconstruction. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_normalizedCarrier_frontier
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 1) ∨
      ∃ V : ℕ, 1 < V ∧
        (Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 V) ∨
          Nonempty (QsOtherFacetPrQuotientCarrierData C P V 1)) := by
  rcases S.pr_locked_direction_unit_or_V_gt_one
      hthree houtThree hnontrivial with hunit | hV
  · left
    rcases hunit with ⟨_hd0, _hd1, hd2, hd3⟩
    exact P.pr_leftQuotientCarrierData hthree houtThree
      (V := 1) (by norm_num) hd2 (by simpa using hd3)
  · rcases hV with ⟨V, hVgt, _hd0, _hd1, horient⟩
    refine Or.inr ⟨V, hVgt, ?_⟩
    rcases horient with hleft | hright
    · exact Or.inl <| P.pr_leftQuotientCarrierData hthree houtThree
        (V := V) (by omega) hleft.1 hleft.2
    · exact Or.inr <| P.pr_rightQuotientCarrierData hthree houtThree
        (V := V) (by omega) hright.1 hright.2

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
