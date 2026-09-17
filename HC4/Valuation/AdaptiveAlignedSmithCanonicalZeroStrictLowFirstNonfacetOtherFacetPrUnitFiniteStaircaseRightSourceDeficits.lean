import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseSupport
import HC4.Polynomial.FiniteStaircaseCrossRoofHullArithmetic
import HC4.Newton.FiniteSupportLowerHullExposure
import Mathlib.Tactic

/-!
# Mirrored source-deficit geometry for the right unit finite staircase

For the right unit orientation retain the literal deficit projection `(e₁,e₃)`.
The locked outside endpoint lies on `e₁=0`, while the primitive highest
endpoint lies on `e₃=0`.  This is the exact transverse mirror of the left unit
source-deficit geometry.
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

/-- Literal source-coordinate wall equation for the right unit staircase. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.support_deficit_wall
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    ((F.highest.n : ℤ) - 1) *
        ((e 0 : ℤ) + (e 3 : ℤ) - 1) =
      (F.locked.ell : ℤ) *
        ((F.highest.n : ℤ) - (e 0 : ℤ) - (e 1 : ℤ)) := by
  have h := (F.support_staircase_equations hthree houtThree he).1
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    one_mul] at h
  push_cast at h
  nlinarith [h]

/-- Right unit staircase deficit/chord identity. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.support_deficit_chord
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    (F.locked.ell : ℤ) * (e 1 : ℤ) +
        ((F.highest.n : ℤ) - 1) * (e 3 : ℤ) =
      (F.locked.ell : ℤ) * ((F.highest.n : ℤ) - 1) +
        ((F.locked.ell : ℤ) + (F.highest.n : ℤ) - 1) *
          (1 - (e 0 : ℤ)) := by
  exact HC4.Polynomial.staircase_source_deficit_chord_identity
    (F.support_deficit_wall hthree houtThree he)

/-- The mirrored deficit projection `(e₁,e₃)` is injective on the right unit
source carrier. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.support_eq_of_deficits_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (h1 : e 1 = f 1) (h3 : e 3 = f 3) : e = f := by
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
  have h3Z : (e 3 : ℤ) = (f 3 : ℤ) := by exact_mod_cast h3
  have h0Z : (e 0 : ℤ) = (f 0 : ℤ) := by
    nlinarith [hew, hfw]
  have h0 : e 0 = f 0 := by exact_mod_cast h0Z

  have hes := (F.support_staircase_equations hthree houtThree he).2
  have hfs := (F.support_staircase_equations hthree houtThree hf).2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    one_mul] at hes hfs
  push_cast at hes hfs
  rw [h0Z, h1Z, h3Z] at hes
  have h2Z : (e 2 : ℤ) = (f 2 : ℤ) := by
    nlinarith [hes, hfs]
  have h2 : e 2 = f 2 := by exact_mod_cast h2Z
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- Literal locked `e₁=0` unit roof point in the right orientation. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.locked_yRoof_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    C.ray.outsideExponent ∈ P.carrier.support ∧
      C.ray.outsideExponent 0 = 1 ∧
      C.ray.outsideExponent 1 = 0 ∧
      C.ray.outsideExponent 2 = F.locked.ell ∧
      C.ray.outsideExponent 3 = F.locked.ell := by
  refine ⟨F.locked.outside_provenance.carrier_mem,
    F.locked.outside_zero, F.locked.outside_one, ?_, F.locked.outside_three⟩
  simpa using F.locked.outside_two

/-- Literal primitive-highest `e₃=0` unit roof point. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.highest_wRoof_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) :
    F.highest.e1 ∈ P.carrier.support ∧
      F.highest.e1 0 = 1 ∧
      F.highest.e1 1 = F.highest.n - 1 ∧
      F.highest.e1 2 = F.highest.n - 1 ∧
      F.highest.e1 3 = 0 := by
  refine ⟨F.highest.e1_provenance.carrier_mem,
    F.highest.e1_zero, F.highest.e1_one, ?_, F.highest.e1_three⟩
  simpa [F.highest_V_eq_one] using F.highest.e1_two

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
