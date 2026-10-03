import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofSourceData
import HC4.Polynomial.RankThreeAffineSupportRealisation
import Mathlib.Tactic

/-!
# Source-honest coordinate control on an exposed cross-roof face

The exact lower-hull equation makes either transverse source coordinate a
valid parameter on the exposed cross-roof face.  This file records the two
injectivity statements and the sharp endpoint bounds needed to extract the
forward and reversed coefficient profiles.
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

namespace QsOtherFacetPrLeftVExposedCrossRoofData

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}

/-- Coordinate `1` is injective on the exact exposed face. -/
theorem face_eq_of_one_eq
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
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
  have h2Z : (e 2 : ℤ) = (f 2 : ℤ) := by
    nlinarith [hec, hfc]
  have h2 : e 2 = f 2 := by exact_mod_cast h2Z
  exact F.support_eq_of_deficits_eq hthree houtThree heP hfP h1 h2

/-- Coordinate `2` is likewise injective on the exact exposed face. -/
theorem face_eq_of_two_eq
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ E.hull.face.support)
    (hf : f ∈ E.hull.face.support)
    (h2 : e 2 = f 2) : e = f := by
  have heP := E.hull.face_support_subset he
  have hfP := E.hull.face_support_subset hf
  have hec := E.hull.cost_eq_of_mem_face he
  have hfc := E.hull.cost_eq_of_mem_face hf
  have h2Z : (e 2 : ℤ) = (f 2 : ℤ) := by exact_mod_cast h2
  have hA : (0 : ℤ) < (E.hull.gap : ℤ) := by
    exact_mod_cast E.hull.gap_pos
  have h1Z : (e 1 : ℤ) = (f 1 : ℤ) := by
    nlinarith [hec, hfc]
  have h1 : e 1 = f 1 := by exact_mod_cast h1Z
  exact F.support_eq_of_deficits_eq hthree houtThree heP hfP h1 h2

/-- Every exposed-face point lies between the two roofs in coordinate `1`. -/
theorem face_one_le_v
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    e 1 ≤ E.v := by
  have hec := E.hull.cost_eq_of_mem_face he
  have hic := E.hull.cost_eq_of_mem_face E.hi_mem_face
  rw [E.hi_one, E.hi_two_zero, E.lo_two] at hic
  norm_num at hic
  have hA : (0 : ℤ) < (E.hull.gap : ℤ) := by
    exact_mod_cast E.hull.gap_pos
  have hBnonneg : (0 : ℤ) ≤ (E.hull.edge 1 : ℤ) := by positivity
  have he2nonneg : (0 : ℤ) ≤ (e 2 : ℤ) := by positivity
  have hmulNonneg :
      (0 : ℤ) ≤ (E.hull.edge 1 : ℤ) * (e 2 : ℤ) :=
    mul_nonneg hBnonneg he2nonneg
  have hscaled :
      (E.hull.gap : ℤ) * (e 1 : ℤ) ≤
        (E.hull.gap : ℤ) * (E.v : ℤ) := by
    calc
      (E.hull.gap : ℤ) * (e 1 : ℤ) ≤
          (E.hull.gap : ℤ) * (e 1 : ℤ) +
            (E.hull.edge 1 : ℤ) * (e 2 : ℤ) :=
        le_add_of_nonneg_right hmulNonneg
      _ = (E.hull.edge 1 : ℤ) * (E.hull.lo 2 : ℤ) := hec
      _ = (E.hull.gap : ℤ) * (E.v : ℤ) := by
        rw [E.lo_two]
        nlinarith [hic]
  have hleZ : (e 1 : ℤ) ≤ (E.v : ℤ) :=
    (mul_le_mul_left hA).mp hscaled
  exact_mod_cast hleZ

/-- Every exposed-face point lies between the two roofs in coordinate `2`. -/
theorem face_two_le_q
    (E : QsOtherFacetPrLeftVExposedCrossRoofData F)
    {e : Fin 4 →₀ ℕ} (he : e ∈ E.hull.face.support) :
    e 2 ≤ E.q := by
  have hec := E.hull.cost_eq_of_mem_face he
  rw [E.lo_two] at hec
  have hB : (0 : ℤ) < (E.hull.edge 1 : ℤ) := by
    exact_mod_cast E.hull.edge_one_pos
  have hAnonneg : (0 : ℤ) ≤ (E.hull.gap : ℤ) := by positivity
  have he1nonneg : (0 : ℤ) ≤ (e 1 : ℤ) := by positivity
  have hmulNonneg :
      (0 : ℤ) ≤ (E.hull.gap : ℤ) * (e 1 : ℤ) :=
    mul_nonneg hAnonneg he1nonneg
  have hscaled :
      (E.hull.edge 1 : ℤ) * (e 2 : ℤ) ≤
        (E.hull.edge 1 : ℤ) * (E.q : ℤ) := by
    calc
      (E.hull.edge 1 : ℤ) * (e 2 : ℤ) ≤
          (E.hull.gap : ℤ) * (e 1 : ℤ) +
            (E.hull.edge 1 : ℤ) * (e 2 : ℤ) :=
        le_add_of_nonneg_left hmulNonneg
      _ = (E.hull.edge 1 : ℤ) * (E.q : ℤ) := hec
  have hleZ : (e 2 : ℤ) ≤ (E.q : ℤ) :=
    (mul_le_mul_left hB).mp hscaled
  exact_mod_cast hleZ

end QsOtherFacetPrLeftVExposedCrossRoofData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
