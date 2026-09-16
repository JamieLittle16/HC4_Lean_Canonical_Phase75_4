import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseClassification
import Mathlib.Tactic

/-!
# A19 finite staircase ordering interface

The surviving left `(1,V)`, `V > 1` carrier lies on the exact wall

    (n - 1) * j = ell * (n - k).

Before coupling the two endpoint first-variation equations, it is useful to
record the only arithmetic structure of this wall that the final argument
needs.  Because `n >= 2` and `ell > 0`, the wall is a genuine one-dimensional
strictly ordered chain:

* the pair degree `k` determines the transverse height `j`;
* the transverse height determines the pair degree;
* increasing pair degree is exactly decreasing transverse height.

The source-facing theorem at the end exposes the corresponding geometric
fact already implicit in the quotient package: two actual carrier monomials
with the same pair degree lie in the same normalized quotient fibre.

No gcd/coprimality assumption is introduced here, and no new carrier package
is created.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- On a non-unit staircase wall, a fixed pair degree has a unique transverse
height. -/
theorem prVGreaterOne_wallSlope_height_eq_of_pair_eq
    (ell n k j₁ j₂ : ℕ)
    (hn : 2 ≤ n)
    (h₁ :
      ((n : ℤ) - 1) * (j₁ : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ)))
    (h₂ :
      ((n : ℤ) - 1) * (j₂ : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    j₁ = j₂ := by
  have hnZ : (0 : ℤ) < (n : ℤ) - 1 := by
    exact_mod_cast (show 1 < n by omega)
  have hjZ : (j₁ : ℤ) = (j₂ : ℤ) := by
    nlinarith [h₁, h₂]
  exact_mod_cast hjZ

/-- Dually, on a non-unit staircase wall a fixed transverse height has a
unique pair degree. -/
theorem prVGreaterOne_wallSlope_pair_eq_of_height_eq
    (ell n k₁ k₂ j : ℕ)
    (hell : 0 < ell)
    (h₁ :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k₁ : ℤ)))
    (h₂ :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k₂ : ℤ))) :
    k₁ = k₂ := by
  have hellZ : (0 : ℤ) < (ell : ℤ) := by exact_mod_cast hell
  have hkZ : (k₁ : ℤ) = (k₂ : ℤ) := by
    nlinarith [h₁, h₂]
  exact_mod_cast hkZ

/-- The staircase order is reversed in `(k,j)`: larger pair degree means
strictly smaller transverse height, and conversely. -/
theorem prVGreaterOne_wallSlope_pair_lt_iff_height_gt
    (ell n k₁ j₁ k₂ j₂ : ℕ)
    (hell : 0 < ell) (hn : 2 ≤ n)
    (h₁ :
      ((n : ℤ) - 1) * (j₁ : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k₁ : ℤ)))
    (h₂ :
      ((n : ℤ) - 1) * (j₂ : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k₂ : ℤ))) :
    k₁ < k₂ ↔ j₂ < j₁ := by
  have hellZ : (0 : ℤ) < (ell : ℤ) := by exact_mod_cast hell
  have hnZ : (0 : ℤ) < (n : ℤ) - 1 := by
    exact_mod_cast (show 1 < n by omega)
  constructor
  · intro hk
    have hkZ : (k₁ : ℤ) < (k₂ : ℤ) := by exact_mod_cast hk
    have hjZ : (j₂ : ℤ) < (j₁ : ℤ) := by
      nlinarith [h₁, h₂]
    exact_mod_cast hjZ
  · intro hj
    have hjZ : (j₂ : ℤ) < (j₁ : ℤ) := by exact_mod_cast hj
    have hkZ : (k₁ : ℤ) < (k₂ : ℤ) := by
      nlinarith [h₁, h₂]
    exact_mod_cast hkZ

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Two actual left-oriented carrier monomials with the same pair degree are
literally in the same normalized `(1,V)` quotient fibre.  This is the small
source-facing interface used by the finite-staircase coupling argument. -/
theorem QsOtherFacetPrLeftVContactFrontierData.support_quotient_eq_of_pair_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair :
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair =
        (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V f).pair) :
    HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e =
      HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V f := by
  have hpairNat : e 0 + e 1 = f 0 + f 1 := by
    simpa [HC4.Polynomial.rankThreeQuotientCoordinate] using hpair
  have hpairZ :
      qsOtherFacetPairDegree .pr e = qsOtherFacetPairDegree .pr f := by
    simp only [qsOtherFacetPairDegree]
    exact_mod_cast hpairNat
  exact F.quotient.pair_fiber he hf hpairZ

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
