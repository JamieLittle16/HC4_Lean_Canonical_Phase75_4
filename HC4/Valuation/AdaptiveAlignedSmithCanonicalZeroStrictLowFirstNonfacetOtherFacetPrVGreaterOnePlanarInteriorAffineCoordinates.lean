import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarInteriorFirstLayer
import Mathlib.Tactic

/-!
# A19 affine coordinates of the first strict-interior planar-contact layer

The first positive planar-contact layer is already known to occupy one full
rank-three quotient fibre.  When strict-interior support exists, the preceding
module identifies its pair degree `k` and first transverse height `j+1`.

This file expands that quotient statement into the literal source exponents.
Every supported monomial of the selected layer has the form

    (t, k-t, j+1-t, V*(k+j-t)),

or equivalently lies on the affine rank-three line with base exponent

    (0, k, j+1, V*(k+j))

and direction `(1,-1,-1,-V)`.  Coefficients remain the literal coefficients of
the source-honest planar carrier.

No degree bound on the resulting one-variable profile is asserted here.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- **Literal affine coordinates of the first strict-interior layer.**

Failure of `NoStrictInteriorSupport` supplies strict-interior integers `k,j`.
For every supported exponent `e` of the first positive planar-contact layer,
the three quotient invariants become the displayed coordinate equations.  The
last conjunct retains exact source coefficient provenance. -/
theorem exists_firstPositiveLayer_strictInterior_affineCoordinates
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport) :
    ∃ k j : ℕ, 1 < k ∧ k < F.highest.n ∧
      0 < j ∧ j < F.locked.ell ∧
      ∀ e ∈ (familyParameterLayer D.family
        (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)).support,
        e 0 + e 1 = k ∧
        e 0 + e 2 = j + 1 ∧
        F.V * e 0 + e 3 = F.V * (k + j) ∧
        MvPolynomial.coeff e (familyParameterLayer D.family
          (firstPositiveActualParameterOrder D.family D.hasPositiveLayer)) =
          MvPolynomial.coeff e P.carrier := by
  rcases D.exists_firstPositiveLayer_strictInterior_fiber
      hthree houtThree hnot with
    ⟨k, j, hkgt, hklt, hjpos, hjlt, hfiber⟩
  refine ⟨k, j, hkgt, hklt, hjpos, hjlt, ?_⟩
  intro e he
  rcases hfiber e he with ⟨hpair, hfirst, hcoeff⟩
  have hpairNat : e 0 + e 1 = k := by
    simpa [rankThreeQuotientCoordinate] using hpair
  have hfirstNat : e 0 + e 2 = j + 1 := by
    simpa [rankThreeQuotientCoordinate] using hfirst
  have heP : e ∈ P.carrier.support :=
    (D.parameterLayer_support_source_and_order he).1
  have hstair := F.support_staircase_equations hthree houtThree heP
  dsimp only at hstair
  have hsecondZ := hstair.2
  simp only [HC4.Polynomial.rankThreeQuotientCoordinate_secondTransverse,
    HC4.Polynomial.rankThreeQuotientCoordinate_pair,
    HC4.Polynomial.rankThreeQuotientCoordinate_firstTransverse,
    one_mul] at hsecondZ
  rw [hpairNat, hfirstNat] at hsecondZ
  have hsecond : F.V * e 0 + e 3 = F.V * (k + j) := by
    have hsecondZ' :
        ((F.V * e 0 + e 3 : ℕ) : ℤ) =
          ((F.V * (k + j) : ℕ) : ℤ) := by
      push_cast at hsecondZ ⊢
      nlinarith
    exact_mod_cast hsecondZ'
  exact ⟨hpairNat, hfirstNat, hsecond, hcoeff⟩

/-- Coordinatewise subtraction form used by the generic affine-line moment
realisation.  The longitudinal coordinate `e 0` is the line parameter. -/
theorem firstPositiveLayer_affine_cast
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    {k j : ℕ}
    {e : Fin 4 →₀ ℕ}
    (hpair : e 0 + e 1 = k)
    (hfirst : e 0 + e 2 = j + 1)
    (hsecond : F.V * e 0 + e 3 = F.V * (k + j)) :
    (fun i : Fin 4 => ((e i : ℕ) : K)) =
      fun i =>
        HC4.Polynomial.rankThreeLogBaseExponent
            (k : K) ((j + 1 : ℕ) : K) ((F.V * (k + j) : ℕ) : K) i +
          (e 0 : K) *
            HC4.Polynomial.rankThreeLogDirection
              (1 : K) (-1 : K) (-1 : K) (-(F.V : K)) i := by
  have hpairK : (e 0 : K) + (e 1 : K) = (k : K) := by
    exact_mod_cast hpair
  have hfirstK : (e 0 : K) + (e 2 : K) = ((j + 1 : ℕ) : K) := by
    exact_mod_cast hfirst
  have hsecondK :
      (F.V : K) * (e 0 : K) + (e 3 : K) =
        (F.V : K) * ((k + j : ℕ) : K) := by
    exact_mod_cast hsecond
  funext i
  fin_cases i
  · simp [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection]
  · simp [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection]
    linear_combination hpairK
  · simp [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection]
    push_cast at hfirstK
    linear_combination hfirstK
  · simp [HC4.Polynomial.rankThreeLogBaseExponent,
      HC4.Polynomial.rankThreeLogDirection]
    push_cast at hsecondK
    linear_combination hsecondK

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
