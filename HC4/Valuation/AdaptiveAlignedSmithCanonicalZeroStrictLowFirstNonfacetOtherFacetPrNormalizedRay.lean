import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrPrimitiveDirection
import Mathlib.Tactic

/-!
# A19 normalized locked PR ray endpoints

The primitive direction normalization combines with the original source-ray
cross relation to put both locked endpoints on an exact monomial curve.

For direction `(1,-1,-1,-V)`:

    facet  = (0,1,k,  V*k),
    outside= (1,0,k-1,V*(k-1)).

Equivalently, coordinate `3` is `V` times coordinate `2` at both endpoints.
For the swapped direction `(1,-1,-V,-1)`, coordinate `2` is `V` times
coordinate `3`.

This is the source-honest origin of the later substitution `Y = y w^V` (or its
transverse swap).
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

/-- In the `(1,-1,-1,-V)` orientation both actual locked source endpoints
satisfy `e3 = V*e2`. -/
theorem qs_ray_pr_normalized_left_endpoint_curve
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1)
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
        -(V : ℤ)) :
    C.ray.facetExponent 3 = V * C.ray.facetExponent 2 ∧
      C.ray.outsideExponent 3 = V * C.ray.outsideExponent 2 := by
  have hcross := (C.qs_ray_pr_outside_base_eq_one_and_cross
    hthree houtThree).2
  have h2Z :
      (C.ray.facetExponent 2 : ℤ) =
        (C.ray.outsideExponent 2 : ℤ) + 1 := by
    omega
  have h3Z :
      (C.ray.facetExponent 3 : ℤ) =
        (C.ray.outsideExponent 3 : ℤ) + (V : ℤ) := by
    omega
  have hcrossZ :
      (C.ray.facetExponent 2 : ℤ) * (C.ray.outsideExponent 3 : ℤ) =
        (C.ray.facetExponent 3 : ℤ) * (C.ray.outsideExponent 2 : ℤ) := by
    exact_mod_cast hcross
  have houtZ :
      (C.ray.outsideExponent 3 : ℤ) =
        (V : ℤ) * (C.ray.outsideExponent 2 : ℤ) := by
    nlinarith
  have hfacetZ :
      (C.ray.facetExponent 3 : ℤ) =
        (V : ℤ) * (C.ray.facetExponent 2 : ℤ) := by
    rw [h2Z, h3Z, houtZ]
    ring
  constructor <;> exact_mod_cast ‹_›

/-- Symmetric endpoint-curve theorem for direction `(1,-1,-V,-1)`. -/
theorem qs_ray_pr_normalized_right_endpoint_curve
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
        -(V : ℤ))
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1) :
    C.ray.facetExponent 2 = V * C.ray.facetExponent 3 ∧
      C.ray.outsideExponent 2 = V * C.ray.outsideExponent 3 := by
  have hcross := (C.qs_ray_pr_outside_base_eq_one_and_cross
    hthree houtThree).2
  have h2Z :
      (C.ray.facetExponent 2 : ℤ) =
        (C.ray.outsideExponent 2 : ℤ) + (V : ℤ) := by
    omega
  have h3Z :
      (C.ray.facetExponent 3 : ℤ) =
        (C.ray.outsideExponent 3 : ℤ) + 1 := by
    omega
  have hcrossZ :
      (C.ray.facetExponent 2 : ℤ) * (C.ray.outsideExponent 3 : ℤ) =
        (C.ray.facetExponent 3 : ℤ) * (C.ray.outsideExponent 2 : ℤ) := by
    exact_mod_cast hcross
  have houtZ :
      (C.ray.outsideExponent 2 : ℤ) =
        (V : ℤ) * (C.ray.outsideExponent 3 : ℤ) := by
    nlinarith
  have hfacetZ :
      (C.ray.facetExponent 2 : ℤ) =
        (V : ℤ) * (C.ray.facetExponent 3 : ℤ) := by
    rw [h2Z, h3Z, houtZ]
    ring
  constructor <;> exact_mod_cast ‹_›

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
