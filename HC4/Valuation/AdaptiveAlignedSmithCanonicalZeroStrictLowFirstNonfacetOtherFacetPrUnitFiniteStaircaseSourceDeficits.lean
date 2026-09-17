import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseSupport
import HC4.Polynomial.FiniteStaircaseCrossRoofHullArithmetic
import HC4.Newton.FiniteSupportLowerHullExposure
import Mathlib.Tactic

/-!
# Source deficit geometry of the unit left finite staircase

For the unit left carrier retain the literal source coordinates
`t=e₀`, `a=e₁`, `b=e₂`.  The staircase wall has the same source-deficit chord
form as in the nonunit branch, and the projection `(e₁,e₂)` remains injective.
The locked outside endpoint lies on the `e₁=0` roof and the primitive-highest
endpoint lies on the `e₂=0` roof.
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

/-- Literal source-coordinate unit staircase wall. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.support_deficit_wall
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    ((F.highest.n : ℤ) - 1) *
        ((e 0 : ℤ) + (e 2 : ℤ) - 1) =
      (F.locked.ell : ℤ) *
        ((F.highest.n : ℤ) - (e 0 : ℤ) - (e 1 : ℤ)) := by
  have h := (F.support_staircase_equations hthree houtThree he).1
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at h
  push_cast at h
  nlinarith [h]

/-- Unit source-deficit chord identity. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.support_deficit_chord
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    (F.locked.ell : ℤ) * (e 1 : ℤ) +
        ((F.highest.n : ℤ) - 1) * (e 2 : ℤ) =
      (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - 1) +
        ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
          (1 - (e 0 : ℤ)) := by
  exact HC4.Polynomial.staircase_source_deficit_chord_identity
    (F.support_deficit_wall hthree houtThree he)

/-- The deficit projection `(e₁,e₂)` is injective on the unit source carrier. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.support_eq_of_deficits_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (h1 : e 1 = f 1) (h2 : e 2 = f 2) :
    e = f := by
  have hew := F.support_deficit_wall hthree houtThree he
  have hfw := F.support_deficit_wall hthree houtThree hf
  have hcoef :
      (0 : ℤ) < ((F.highest.n : ℤ) - 1) + (F.locked.ell : ℤ) := by
    have hn : (1 : ℤ) < (F.highest.n : ℤ) := by
      exact_mod_cast (show 1 < F.highest.n by omega)
    have hell : (0 : ℤ) < (F.locked.ell : ℤ) := by
      exact_mod_cast F.locked.ell_pos
    omega
  have h1Z : (e 1 : ℤ) = (f 1 : ℤ) := by exact_mod_cast h1
  have h2Z : (e 2 : ℤ) = (f 2 : ℤ) := by exact_mod_cast h2
  have h0Z : (e 0 : ℤ) = (f 0 : ℤ) := by
    nlinarith [hew, hfw]
  have h0 : e 0 = f 0 := by exact_mod_cast h0Z

  have hes := (F.support_staircase_equations hthree houtThree he).2
  have hfs := (F.support_staircase_equations hthree houtThree hf).2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at hes hfs
  push_cast at hes hfs
  rw [h0Z, h1Z, h2Z] at hes
  have h3Z : (e 3 : ℤ) = (f 3 : ℤ) := by
    nlinarith [hes, hfs]
  have h3 : e 3 = f 3 := by exact_mod_cast h3Z
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Literal locked `e₁=0` unit roof point. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.locked_yRoof_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R) :
    C.ray.outsideExponent ∈ P.carrier.support ∧
      C.ray.outsideExponent 0 = 1 ∧
      C.ray.outsideExponent 1 = 0 ∧
      C.ray.outsideExponent 2 = F.locked.ell ∧
      C.ray.outsideExponent 3 = F.locked.ell := by
  refine ⟨F.locked.outside_provenance.carrier_mem,
    F.locked.outside_zero, F.locked.outside_one,
    F.locked.outside_two, ?_⟩
  simpa using F.locked.outside_three

/-- Literal primitive-highest `e₂=0` unit roof point. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.highest_zRoof_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R) :
    F.highest.e1 ∈ P.carrier.support ∧
      F.highest.e1 0 = 1 ∧
      F.highest.e1 1 = F.highest.n - 1 ∧
      F.highest.e1 2 = 0 ∧
      F.highest.e1 3 = F.highest.n - 1 := by
  refine ⟨F.highest.e1_provenance.carrier_mem,
    F.highest.e1_zero, F.highest.e1_one, F.highest.e1_two, ?_⟩
  simpa [F.highest_V_eq_one] using F.highest.e1_three

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
