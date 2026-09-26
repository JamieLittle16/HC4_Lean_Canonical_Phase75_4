import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseSourceDeficits
import Mathlib.Tactic

/-!
# Mirrored source-deficit geometry for the right finite staircase

The right `(V,1)` orientation is the transverse-coordinate swap of the left
`(1,V)` staircase.  We keep the actual source carrier and simply use the
literal deficit projection `(e₁,e₃)`.  The already-verified right staircase
equations then give the same chord relation as on the left, with coordinate
`3` replacing coordinate `2`.
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

/-- Literal source-coordinate wall equation for the right `(V,1)` staircase. -/
theorem QsOtherFacetPrRightVContactFrontierData.support_deficit_wall
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
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

/-- Right staircase deficit/chord identity on the actual source support. -/
theorem QsOtherFacetPrRightVContactFrontierData.support_deficit_chord
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
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

/-- The mirrored deficit projection `(e₁,e₃)` is injective on the right
source-honest carrier. -/
theorem QsOtherFacetPrRightVContactFrontierData.support_eq_of_deficits_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (h1 : e 1 = f 1) (h3 : e 3 = f 3) :
    e = f := by
  have hew := F.support_deficit_wall hthree houtThree he
  have hfw := F.support_deficit_wall hthree houtThree hf
  have hcoef :
      (0 : ℤ) <
        ((F.highest.n : ℤ) - 1) + (F.locked.ell : ℤ) := by
    have hn2 : 2 ≤ F.highest.n := F.highest.n_two_le
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

/-- The locked outside endpoint is the literal `e₁=0` roof point in the
right orientation. -/
theorem QsOtherFacetPrRightVContactFrontierData.locked_yRoof_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) :
    C.ray.outsideExponent ∈ P.carrier.support ∧
      C.ray.outsideExponent 0 = 1 ∧
      C.ray.outsideExponent 1 = 0 ∧
      C.ray.outsideExponent 2 = F.locked.ell * F.V ∧
      C.ray.outsideExponent 3 = F.locked.ell := by
  exact ⟨F.locked.outside_provenance.carrier_mem,
    F.locked.outside_zero, F.locked.outside_one,
    F.locked.outside_two, F.locked.outside_three⟩

/-- The primitive highest endpoint is the literal `e₃=0` roof point. -/
theorem QsOtherFacetPrRightVContactFrontierData.highest_wRoof_mem
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) :
    F.highest.e1 ∈ P.carrier.support ∧
      F.highest.e1 0 = 1 ∧
      F.highest.e1 1 = F.highest.n - 1 ∧
      F.highest.e1 2 = F.V * (F.highest.n - 1) ∧
      F.highest.e1 3 = 0 := by
  refine ⟨F.highest.e1_provenance.carrier_mem,
    F.highest.e1_zero, F.highest.e1_one, ?_, F.highest.e1_three⟩
  simpa [F.highest_V_eq] using F.highest.e1_two

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
