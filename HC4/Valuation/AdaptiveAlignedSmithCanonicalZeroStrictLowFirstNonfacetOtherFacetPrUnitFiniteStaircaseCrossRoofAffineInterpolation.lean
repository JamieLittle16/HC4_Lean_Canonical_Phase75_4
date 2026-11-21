import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCrossRoofAffineCoordinates
import Mathlib.Tactic

/-!
# Exact affine interpolation on the exposed unit cross-roof face

The unit lower-hull face is one-dimensional in the literal source coordinates.
The hull cost gives the transverse interpolation relation, the source deficit
chord determines coordinate `0`, and the unit staircase curve determines
coordinate `3`.  These are the exact source identities needed for the two
rank-three affine-line realisations.
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

namespace QsOtherFacetPrUnitLeftExposedCrossRoofData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitLeftContactFrontierData C P S R}

/-- The lower-hull cost equation normalized by the two roof endpoints. -/
theorem face_cross_relation
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    (E.v : ℤ) * (e 2 : ℤ) + (E.q : ℤ) * (e 1 : ℤ) =
      (E.q : ℤ) * (E.v : ℤ) := by
  have hec := E.hull.cost_eq_of_mem_face he
  have hic := E.hull.cost_eq_of_mem_face E.hi_mem_face
  rw [E.lo_two] at hec
  rw [E.hi_one, E.hi_two_zero, E.lo_two] at hic
  norm_num at hic
  have hBne : (E.hull.edge 1 : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt E.hull.edge_one_pos)
  have hfactor :
      (E.hull.edge 1 : ℤ) *
        ((E.v : ℤ) * (e 2 : ℤ) +
          (E.q : ℤ) * (e 1 : ℤ) -
          (E.q : ℤ) * (E.v : ℤ)) = 0 := by
    linear_combination
      (E.v : ℤ) * hec - (e 1 : ℤ) * hic
  have hz := (mul_eq_zero.mp hfactor).resolve_left hBne
  linarith

/-- The unit staircase curve in literal source coordinates. -/
theorem face_curve_relation
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    (e 3 : ℤ) =
      (e 0 : ℤ) + (e 1 : ℤ) + (e 2 : ℤ) - 1 := by
  have heP := E.hull.face_support_subset he
  have hs := (F.support_staircase_equations hthree houtThree heP).2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at hs
  push_cast at hs
  nlinarith [hs]

/-- Coordinate `0` interpolates affinely between the two literal roof
endpoints, with coordinate `1` as parameter. -/
theorem face_zero_interpolation
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    (E.v : ℤ) * ((e 0 : ℤ) - (E.kLo : ℤ)) =
      (e 1 : ℤ) * (((E.jHi + 1 : ℕ) : ℤ) - (E.kLo : ℤ)) := by
  have heP := E.hull.face_support_subset he
  have hhiP := E.hull.face_support_subset E.hi_mem_face
  have hec := F.support_deficit_chord hthree houtThree heP
  have hloc := F.support_deficit_chord hthree houtThree E.hull.lo_mem
  have hhic := F.support_deficit_chord hthree houtThree hhiP
  rw [E.hull.lo_one_zero, E.lo_zero, E.lo_two] at hloc
  rw [E.hi_zero, E.hi_one, E.hi_two_zero] at hhic
  norm_num at hloc hhic
  have hcross := E.face_cross_relation he
  have hCpos :
      (0 : ℤ) <
        (F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1 := by
    have hell : (0 : ℤ) < (F.locked.ell : ℤ) := by
      exact_mod_cast F.locked.ell_pos
    have hn2 : (2 : ℤ) ≤ (F.highest.n : ℤ) := by
      exact_mod_cast F.highest.n_two_le
    nlinarith only [hell, hn2]
  have hjHiSucc :
      (((E.jHi + 1 : ℕ) : ℤ)) = (E.jHi : ℤ) + 1 := by
    push_cast
    ring
  have hfactor :
      ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
        ((E.v : ℤ) * ((e 0 : ℤ) - (E.kLo : ℤ)) -
          (e 1 : ℤ) *
            (((E.jHi + 1 : ℕ) : ℤ) - (E.kLo : ℤ))) = 0 := by
    rw [hjHiSucc]
    linear_combination
      (E.v : ℤ) * hec -
      (E.v : ℤ) * hloc -
      (e 1 : ℤ) * hhic +
      (e 1 : ℤ) * hloc -
      ((F.highest.n : ℤ) - 1) * hcross
  have hz := (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hCpos)
  linarith

/-- Coordinate `3` interpolates affinely between the same two literal roof
endpoints. -/
theorem face_three_interpolation
    (E : QsOtherFacetPrUnitLeftExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    (E.v : ℤ) * ((e 3 : ℤ) - (E.hull.lo 3 : ℤ)) =
      (e 1 : ℤ) * ((E.hi 3 : ℤ) - (E.hull.lo 3 : ℤ)) := by
  have hec := E.face_curve_relation hthree houtThree he
  have hloc := E.face_curve_relation hthree houtThree E.hull.lo_mem_face
  have hhic := E.face_curve_relation hthree houtThree E.hi_mem_face
  have hzero := E.face_zero_interpolation hthree houtThree he
  have hcross := E.face_cross_relation he
  rw [E.hull.lo_one_zero, E.lo_zero, E.lo_two] at hloc
  rw [E.hi_zero, E.hi_one, E.hi_two_zero] at hhic
  norm_num at hloc hhic
  have hjHiSucc :
      (((E.jHi + 1 : ℕ) : ℤ)) = (E.jHi : ℤ) + 1 := by
    push_cast
    ring
  rw [hjHiSucc] at hzero
  linear_combination
    (E.v : ℤ) * hec -
    (E.v : ℤ) * hloc -
    (e 1 : ℤ) * hhic +
    (e 1 : ℤ) * hloc +
    hzero + hcross

end QsOtherFacetPrUnitLeftExposedCrossRoofData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
