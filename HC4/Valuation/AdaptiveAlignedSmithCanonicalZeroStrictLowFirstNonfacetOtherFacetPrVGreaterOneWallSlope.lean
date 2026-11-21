import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneContactFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarWallRatio
import Mathlib.Tactic

/-!
# A19 finite wall slope on the non-unit PR frontier

Once the locked pair and primitive highest pair are written in the common
`V>1` orientation, the retained maximal-ratio wall has a very small arithmetic
content.

Write a further left-oriented primitive pair at pair degree `k` and `H`-height
`j` as

    (0,k,j+1,V(k+j)) -- (1,k-1,j,V(k+j-1)).

Comparing its wall ratio with the highest pair of degree `n`, while the locked
ray has height `ell`, gives

    (V-1) * ((n-1)j - ell(n-k)) = 0.

Thus on the non-unit branch

    (n-1)j = ell(n-k).

The swapped `(V,1)` orientation has the same final equation.  This file proves
that cancellation directly from the *actual retained source wall equation*.
No contact or blocker clocks are compared.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped BigOperators

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem finsupp_weight_explicit_fin4
    (a : Fin 4 → ℤ) (e : Fin 4 →₀ ℕ) :
    Finsupp.weight a e =
      a 0 * (e 0 : ℤ) + a 1 * (e 1 : ℤ) +
      a 2 * (e 2 : ℤ) + a 3 * (e 3 : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · rw [Fin.sum_univ_four]
    ring
  · intro i
    simp

/-- State-free cancellation behind both non-unit orientations. -/
theorem prVGreaterOne_wallSlope_arithmetic
    (V ell n k j : ℕ)
    (hV : 1 < V)
    (hwall :
      ((n : ℤ) - 1) *
          ((j : ℤ) * (1 - (V : ℤ)) +
            (ell : ℤ) * (2 * (V : ℤ) * (k : ℤ) - (V : ℤ) - 1)) =
        ((k : ℤ) - 1) *
          ((ell : ℤ) *
            (2 * (V : ℤ) * (n : ℤ) - (V : ℤ) - 1))) :
    ((n : ℤ) - 1) * (j : ℤ) =
      (ell : ℤ) * ((n : ℤ) - (k : ℤ)) := by
  have hVne : (V : ℤ) - 1 ≠ 0 := by
    have hVz : (1 : ℤ) < (V : ℤ) := by exact_mod_cast hV
    omega
  have hfactor :
      ((V : ℤ) - 1) *
          (((n : ℤ) - 1) * (j : ℤ) -
            (ell : ℤ) * ((n : ℤ) - (k : ℤ))) = 0 := by
    calc
      ((V : ℤ) - 1) *
          (((n : ℤ) - 1) * (j : ℤ) -
            (ell : ℤ) * ((n : ℤ) - (k : ℤ))) =
        -(((n : ℤ) - 1) *
            ((j : ℤ) * (1 - (V : ℤ)) +
              (ell : ℤ) *
                (2 * (V : ℤ) * (k : ℤ) - (V : ℤ) - 1)) -
          ((k : ℤ) - 1) *
            ((ell : ℤ) *
              (2 * (V : ℤ) * (n : ℤ) - (V : ℤ) - 1))) := by ring
      _ = 0 := by rw [hwall]; ring
  have hzero := (mul_eq_zero.mp hfactor).resolve_left hVne
  linarith

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Actual source-wall interpolation in the `(1,V)` orientation.  The input
`e` is only assumed to be an actual carrier support point with the displayed
left staircase coordinates; no global claim that every support point has this
shape is made here. -/
theorem QsOtherFacetPrLeftVContactFrontierData.wallSlope_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {e : Fin 4 →₀ ℕ} {k j : ℕ}
    (he : e ∈ P.carrier.support)
    (he0 : e 0 = 0) (he1 : e 1 = k)
    (he2 : e 2 = j + 1) (he3 : e 3 = F.V * (k + j)) :
    ((F.highest.n : ℤ) - 1) * (j : ℤ) =
      (F.locked.ell : ℤ) *
        ((F.highest.n : ℤ) - (k : ℤ)) := by
  have hwall := P.support_wall_ratio he F.highest.e0_provenance.carrier_mem
  have hpairE : qsOtherFacetPairDegree .pr e = (k : ℤ) := by
    simp [qsOtherFacetPairDegree, he0, he1]
  have hpairH :
      qsOtherFacetPairDegree .pr F.highest.e0 = (F.highest.n : ℤ) := by
    simp [qsOtherFacetPairDegree, F.highest.e0_zero, F.highest.e0_one]
  have hskewE :
      Finsupp.weight (qsOtherFacetSkewWeight C .pr) e -
          qsOtherFacetSkewLevel C .pr =
        (j : ℤ) * (1 - (F.V : ℤ)) +
          (F.locked.ell : ℤ) *
            (2 * (F.V : ℤ) * (k : ℤ) - (F.V : ℤ) - 1) := by
    rw [finsupp_weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      F.locked.facet_two, F.locked.facet_three,
      F.locked.outside_two, F.locked.outside_three,
      he0, he1, he2, he3]
    push_cast
    ring
  have hskewH :
      Finsupp.weight (qsOtherFacetSkewWeight C .pr) F.highest.e0 -
          qsOtherFacetSkewLevel C .pr =
        (F.locked.ell : ℤ) *
          (2 * (F.V : ℤ) * (F.highest.n : ℤ) - (F.V : ℤ) - 1) := by
    rw [finsupp_weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      F.locked.facet_two, F.locked.facet_three,
      F.locked.outside_two, F.locked.outside_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq]
    push_cast
    ring
  rw [hpairE, hpairH, hskewE, hskewH] at hwall
  exact prVGreaterOne_wallSlope_arithmetic
    F.V F.locked.ell F.highest.n k j F.V_gt_one hwall

/-- Swapped source-wall interpolation in the `(V,1)` orientation. -/
theorem QsOtherFacetPrRightVContactFrontierData.wallSlope_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    {e : Fin 4 →₀ ℕ} {k j : ℕ}
    (he : e ∈ P.carrier.support)
    (he0 : e 0 = 0) (he1 : e 1 = k)
    (he2 : e 2 = F.V * (k + j)) (he3 : e 3 = j + 1) :
    ((F.highest.n : ℤ) - 1) * (j : ℤ) =
      (F.locked.ell : ℤ) *
        ((F.highest.n : ℤ) - (k : ℤ)) := by
  have hwall := P.support_wall_ratio he F.highest.e0_provenance.carrier_mem
  have hpairE : qsOtherFacetPairDegree .pr e = (k : ℤ) := by
    simp [qsOtherFacetPairDegree, he0, he1]
  have hpairH :
      qsOtherFacetPairDegree .pr F.highest.e0 = (F.highest.n : ℤ) := by
    simp [qsOtherFacetPairDegree, F.highest.e0_zero, F.highest.e0_one]
  have hskewE :
      Finsupp.weight (qsOtherFacetSkewWeight C .pr) e -
          qsOtherFacetSkewLevel C .pr =
        -((j : ℤ) * (1 - (F.V : ℤ)) +
          (F.locked.ell : ℤ) *
            (2 * (F.V : ℤ) * (k : ℤ) - (F.V : ℤ) - 1)) := by
    rw [finsupp_weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      F.locked.facet_two, F.locked.facet_three,
      F.locked.outside_two, F.locked.outside_three,
      he0, he1, he2, he3]
    push_cast
    ring
  have hskewH :
      Finsupp.weight (qsOtherFacetSkewWeight C .pr) F.highest.e0 -
          qsOtherFacetSkewLevel C .pr =
        -((F.locked.ell : ℤ) *
          (2 * (F.V : ℤ) * (F.highest.n : ℤ) - (F.V : ℤ) - 1)) := by
    rw [finsupp_weight_explicit_fin4]
    simp [qsOtherFacetSkewWeight, qsOtherFacetSkewLevel,
      F.locked.facet_two, F.locked.facet_three,
      F.locked.outside_two, F.locked.outside_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq]
    push_cast
    ring
  rw [hpairE, hpairH, hskewE, hskewH] at hwall
  have hwall' :
      ((F.highest.n : ℤ) - 1) *
          ((j : ℤ) * (1 - (F.V : ℤ)) +
            (F.locked.ell : ℤ) *
              (2 * (F.V : ℤ) * (k : ℤ) - (F.V : ℤ) - 1)) =
        ((k : ℤ) - 1) *
          ((F.locked.ell : ℤ) *
            (2 * (F.V : ℤ) * (F.highest.n : ℤ) - (F.V : ℤ) - 1)) := by
    linarith
  exact prVGreaterOne_wallSlope_arithmetic
    F.V F.locked.ell F.highest.n k j F.V_gt_one hwall'

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
