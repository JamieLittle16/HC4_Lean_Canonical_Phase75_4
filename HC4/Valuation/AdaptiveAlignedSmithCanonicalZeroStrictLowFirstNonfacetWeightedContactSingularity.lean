import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetIntegralLockedFrontier
import HC4.Polynomial.MaximalHessianInitial
import HC4.MongeAmpere.PolynomialInitial
import Mathlib.Tactic

/-!
# A19.100: the actual integral first-contact face is Hessian singular

A19.97/A19.98 produce an honest integral source weight on the represented
zero-clock special fibre.  This file applies the generic maximal Hessian
initial-form identity directly to that actual source.

For the lower `.qs` contact with integral slope `r`, use source weights

    w_0 = r + 1,   w_1 = w_2 = w_3 = 1.

Then `Finsupp.weight w d = ordinaryDegree4 d + r*d[0]`.  The special fibre is
bounded above by `D = T.topFace.degree` for this weight.  Since the represented
zero-clock special fibre has Hessian determinant exactly one, the determinant
of its maximal `D`-contact face is the determinant initial form at weight

    4*D - 2*(r+4).

The retained strict-low source witness has ordinary degree at least three and
`d[0] >= 2`; together with `r >= 2` this makes that determinant weight strictly
positive.  Hence the corresponding initial form of the constant determinant
`1` vanishes, so the actual weighted contact face is Hessian singular.

This is the source-native Hessian identity needed by the staircase-profile
bridge.  No planar terminal, balance assumption, or new progress measure is
introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Integral first-contact weight for the lower `.qs` chart. -/
def qsIntegralContactWeight (r : ℕ) (i : Fin 4) : ℤ :=
  if i = (0 : Fin 4) then (r : ℤ) + 1 else 1

/-- The integral contact weight is exactly ordinary degree plus `r` times the
omitted `.qs` coordinate. -/
theorem qsIntegralContactWeight_eq
    (r : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (qsIntegralContactWeight r) d =
      (HC4.Polynomial.ordinaryDegree4 d + r * d (0 : Fin 4) : ℕ) := by
  rw [Finsupp.weight_apply]
  simp [qsIntegralContactWeight, Finsupp.sum_fintype,
    HC4.Polynomial.ordinaryDegree4, Fin.sum_univ_four]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

-- CI anchor: compile the source-native weighted-contact singularity after inventory refresh.

/-- **A19.100 source-native weighted-contact singularity.**  In the genuine
lower `.qs` other-facet branch, the integral contact slope exposes an actual
maximal weighted initial form of the represented special fibre whose Hessian
determinant is zero. -/
theorem qs_ray_otherFacet_weightedContact_hessianDeterminant_eq_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {next : ToricFacet}
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    ∃ r : ℕ,
      2 ≤ r ∧
      HC4.Polynomial.IsWeightLE
        (qsIntegralContactWeight r) (T.topFace.degree : ℤ)
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ∧
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.initialForm
          (qsIntegralContactWeight r) (T.topFace.degree : ℤ)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family)) = 0 := by
  rcases C.qs_ray_otherFacet_integral_locked_source_contact
      hthree hne houtThree with
    ⟨r, hr, _hbump, hsource, _hray, _hlock⟩
  let F : MvPolynomial (Fin 4) K :=
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  let D : ℕ := T.topFace.degree
  have hLE : HC4.Polynomial.IsWeightLE
      (qsIntegralContactWeight r) (D : ℤ) F := by
    intro d hd
    rw [qsIntegralContactWeight_eq]
    exact_mod_cast hsource hd
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨d, hd, hdeg, hd0, _hcodim⟩
  have hcontact := hsource hd
  have hmul : r * 2 ≤ r * d (0 : Fin 4) :=
    Nat.mul_le_mul_left r hd0
  have hDnat : 3 + 2 * r ≤ D := by
    dsimp [D]
    omega
  have hsum :
      (∑ i : Fin 4, qsIntegralContactWeight r i) = (r : ℤ) + 4 := by
    simp [qsIntegralContactWeight, Fin.sum_univ_four]
    ring
  have hlevel :
      0 < (Fintype.card (Fin 4) : ℤ) * (D : ℤ) -
        2 * ∑ i : Fin 4, qsIntegralContactWeight r i := by
    rw [hsum]
    simp only [Fintype.card_fin]
    have hDint : (3 + 2 * r : ℕ) ≤ D := hDnat
    have hDint' : ((3 + 2 * r : ℕ) : ℤ) ≤ (D : ℤ) := by
      exact_mod_cast hDint
    have hr' : (2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    omega
  have hMA : HC4.MongeAmpere.IsPolynomialMongeAmpere F := by
    dsimp [F]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hzero :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.initialForm
          (qsIntegralContactWeight r) (D : ℤ) F) = 0 := by
    rw [← HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
      (qsIntegralContactWeight r) (D : ℤ) F hLE]
    apply HC4.MongeAmpere.initialForm_hessianDeterminant_eq_zero hMA
    exact hlevel
  exact ⟨r, hr, hLE, by simpa [F, D] using hzero⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
