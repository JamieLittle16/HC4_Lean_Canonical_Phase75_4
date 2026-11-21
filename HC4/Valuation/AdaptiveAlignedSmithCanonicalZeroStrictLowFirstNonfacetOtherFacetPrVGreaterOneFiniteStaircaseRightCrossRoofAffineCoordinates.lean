import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCrossRoofSourceData
import HC4.Polynomial.RankThreeAffineSupportRealisation
import Mathlib.Tactic

/-!
# Source-honest coordinate control on a mirrored exposed cross-roof face

The exact mirrored lower-hull equation makes either transverse source
coordinate a valid parameter on the exposed cross-roof face.  This is the
right `(V,1)` counterpart of the already-rooted left affine-coordinate layer.
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

namespace QsOtherFacetPrRightVExposedCrossRoofData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrRightVContactFrontierData C P S R}

/-- Coordinate `1` is injective on the exact mirrored exposed face. -/
theorem face_eq_of_one_eq
    (E : QsOtherFacetPrRightVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ E.hull.face.support)
    (hf : f ∈ E.hull.face.support)
    (h1 : e 1 = f 1) : e = f := by
  have heP := E.hull.face_support_subset he
  have hfP := E.hull.face_support_subset hf
  have hec := E.hull.cost_eq_of_mem_face he
  have hfc := E.hull.cost_eq_of_mem_face hf
  have h1Z : (e 1 : ℤ) = (f 1 : ℤ) := by exact_mod_cast h1
  have hB : (0 : ℤ) < (E.hull.edge 1 : ℤ) := by
    exact_mod_cast E.hull.edge_one_pos
  have h3Z : (e 3 : ℤ) = (f 3 : ℤ) := by
    nlinarith [hec, hfc]
  have h3 : e 3 = f 3 := by exact_mod_cast h3Z
  exact F.support_eq_of_deficits_eq hthree houtThree heP hfP h1 h3

/-- Coordinate `3` is likewise injective on the exact mirrored exposed face. -/
theorem face_eq_of_three_eq
    (E : QsOtherFacetPrRightVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ E.hull.face.support)
    (hf : f ∈ E.hull.face.support)
    (h3 : e 3 = f 3) : e = f := by
  have heP := E.hull.face_support_subset he
  have hfP := E.hull.face_support_subset hf
  have hec := E.hull.cost_eq_of_mem_face he
  have hfc := E.hull.cost_eq_of_mem_face hf
  have h3Z : (e 3 : ℤ) = (f 3 : ℤ) := by exact_mod_cast h3
  have hA : (0 : ℤ) < (E.hull.gap : ℤ) := by
    exact_mod_cast E.hull.gap_pos
  have h1Z : (e 1 : ℤ) = (f 1 : ℤ) := by
    nlinarith [hec, hfc]
  have h1 : e 1 = f 1 := by exact_mod_cast h1Z
  exact F.support_eq_of_deficits_eq hthree houtThree heP hfP h1 h3

/-- Every mirrored exposed-face point lies between the roofs in coordinate `1`. -/
theorem face_one_le_v
    (E : QsOtherFacetPrRightVExposedCrossRoofData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    e 1 ≤ E.v := by
  have hec := E.hull.cost_eq_of_mem_face he
  have hic := E.hull.cost_eq_of_mem_face E.hi_mem_face
  rw [E.hi_one, E.hi_three_zero, E.lo_three] at hic
  norm_num at hic
  have hA : (0 : ℤ) < (E.hull.gap : ℤ) := by
    exact_mod_cast E.hull.gap_pos
  have hBnonneg : (0 : ℤ) ≤ (E.hull.edge 1 : ℤ) := by positivity
  have he3nonneg : (0 : ℤ) ≤ (e 3 : ℤ) := by positivity
  have hmulNonneg :
      (0 : ℤ) ≤ (E.hull.edge 1 : ℤ) * (e 3 : ℤ) :=
    mul_nonneg hBnonneg he3nonneg
  have hscaled :
      (E.hull.gap : ℤ) * (e 1 : ℤ) ≤
        (E.hull.gap : ℤ) * (E.v : ℤ) := by
    calc
      (E.hull.gap : ℤ) * (e 1 : ℤ) ≤
          (E.hull.gap : ℤ) * (e 1 : ℤ) +
            (E.hull.edge 1 : ℤ) * (e 3 : ℤ) :=
        le_add_of_nonneg_right hmulNonneg
      _ = (E.hull.edge 1 : ℤ) * (E.hull.lo 3 : ℤ) := hec
      _ = (E.hull.gap : ℤ) * (E.v : ℤ) := by
        rw [E.lo_three]
        nlinarith [hic]
  have hleZ : (e 1 : ℤ) ≤ (E.v : ℤ) :=
    (mul_le_mul_left hA).mp hscaled
  exact_mod_cast hleZ

/-- Every mirrored exposed-face point lies between the roofs in coordinate `3`. -/
theorem face_three_le_q
    (E : QsOtherFacetPrRightVExposedCrossRoofData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    e 3 ≤ E.q := by
  have hec := E.hull.cost_eq_of_mem_face he
  rw [E.lo_three] at hec
  have hB : (0 : ℤ) < (E.hull.edge 1 : ℤ) := by
    exact_mod_cast E.hull.edge_one_pos
  have hAnonneg : (0 : ℤ) ≤ (E.hull.gap : ℤ) := by positivity
  have he1nonneg : (0 : ℤ) ≤ (e 1 : ℤ) := by positivity
  have hmulNonneg :
      (0 : ℤ) ≤ (E.hull.gap : ℤ) * (e 1 : ℤ) :=
    mul_nonneg hAnonneg he1nonneg
  have hscaled :
      (E.hull.edge 1 : ℤ) * (e 3 : ℤ) ≤
        (E.hull.edge 1 : ℤ) * (E.q : ℤ) := by
    calc
      (E.hull.edge 1 : ℤ) * (e 3 : ℤ) ≤
          (E.hull.gap : ℤ) * (e 1 : ℤ) +
            (E.hull.edge 1 : ℤ) * (e 3 : ℤ) :=
        le_add_of_nonneg_left hmulNonneg
      _ = (E.hull.edge 1 : ℤ) * (E.q : ℤ) := hec
  have hleZ : (e 3 : ℤ) ≤ (E.q : ℤ) :=
    (mul_le_mul_left hB).mp hscaled
  exact_mod_cast hleZ

end QsOtherFacetPrRightVExposedCrossRoofData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
