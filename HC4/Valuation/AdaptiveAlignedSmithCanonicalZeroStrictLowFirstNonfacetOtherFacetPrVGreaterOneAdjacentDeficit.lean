import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseSourceDeficits
import HC4.Polynomial.FiniteStaircaseAdjacentDeficit
import Mathlib.Tactic

/-!
# Source-facing adjacent-deficit exclusion

The state-free finite-staircase arithmetic says that two source points on the
live left staircase cannot have adjacent deficit pairs at equal total deficit.
This file attaches that statement to the actual source-honest planar carrier.
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

/-- **Adjacent deficit pairs cannot both occur in the actual left non-unit
carrier.** -/
theorem QsOtherFacetPrLeftVContactFrontierData.no_adjacent_deficits
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support)
    (hf : f ∈ P.carrier.support)
    (hf1 : f 1 = e 1 + 1)
    (he2 : e 2 = f 2 + 1) :
    False := by
  have hnell : F.highest.n ≤ F.locked.ell := by
    have hlt := F.highest_n_lt_locked_height hthree houtThree
    omega
  exact HC4.Polynomial.no_adjacent_deficits_on_staircase_chord
    F.highest.n_two_le hnell
    (F.support_deficit_chord hthree houtThree he)
    (F.support_deficit_chord hthree houtThree hf)
    hf1 he2

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
