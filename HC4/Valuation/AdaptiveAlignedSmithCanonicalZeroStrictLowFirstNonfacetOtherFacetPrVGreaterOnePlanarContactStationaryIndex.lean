import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactLayerAffineProfile
import Mathlib.Tactic

/-!
# A19 stationary indexing of the planar-contact staircase

The singular planar-contact Rees is indexed by its honest reverse-Rees order
`q`, while the stationary staircase rigidity package is written in the
weighted binary form `D - r*m`.

The retained contact interpolation gives, for a layer of pair degree `k`,

    (n - 1) q = B (k - 1),

where

    B = (V + 1) (ell + 1 - n)

and `n` is the primitive highest pair degree.  Reindexing from the highest pair
by `m = n-k` turns this literally into

    (n - 1) q = D - B m,
    D = B (n - 1).

This file freezes that identification source-honestly.  In particular the
stationary weight `B` is at least two (indeed at least three) in the live
`V > 1` branch.  No determinant or rigidity conclusion is used here.
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

namespace QsOtherFacetPrLeftVContactFrontierData

/-- The positive stationary staircase weight carried by the locked-to-highest
contact gap. -/
def stationaryWeight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) : ℕ :=
  (F.V + 1) * (F.locked.ell + 1 - F.highest.n)

/-- Total weighted degree after reindexing the highest pair to index zero. -/
def stationaryTotalDegree
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) : ℕ :=
  F.stationaryWeight * (F.highest.n - 1)

/-- Stationary index of a pair degree, counted downwards from the primitive
highest pair. -/
def stationaryIndex
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (k : ℕ) : ℕ :=
  F.highest.n - k

/-- The stationary weight is genuinely positive. -/
theorem stationaryWeight_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    0 < F.stationaryWeight := by
  unfold stationaryWeight
  have hdiff : 0 < F.locked.ell + 1 - F.highest.n := by
    have hlt := F.highest_n_lt_locked_height hthree houtThree
    omega
  exact Nat.mul_pos (by omega) hdiff

/-- In the non-unit branch the stationary weight satisfies the hypothesis
`r >= 2` required by the finite staircase rigidity theorem. -/
theorem two_le_stationaryWeight
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    2 ≤ F.stationaryWeight := by
  unfold stationaryWeight
  have hdiff : 1 ≤ F.locked.ell + 1 - F.highest.n := by
    have hlt := F.highest_n_lt_locked_height hthree houtThree
    omega
  have hmul := Nat.mul_le_mul_left (F.V + 1) hdiff
  simp only [Nat.mul_one] at hmul
  have hVgt : 1 < F.V := F.V_gt_one
  have hV : 3 ≤ F.V + 1 := by omega
  omega

end QsOtherFacetPrLeftVContactFrontierData

namespace QsOtherFacetPrLeftVParameterAffineLayerData

/-- **Exact stationary reindexing of every nonzero planar-contact layer.**

After multiplying the honest parameter order by `n-1`, a layer of pair degree
`k` occurs at the standard stationary weighted order `D-r*m`, with
`m = n-k`, `r = B`, and `D = B(n-1)`. -/
theorem stationary_scaledOrder_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (F.highest.n - 1) * order =
      F.stationaryTotalDegree -
        F.stationaryWeight * F.stationaryIndex A.k := by
  rcases MvPolynomial.support_nonempty.mpr A.layer_ne with ⟨e, he⟩
  have hinterp := D.parameterLayer_contactOrder_interpolation
    hthree houtThree he
  have hpair :
      (HC4.Polynomial.rankThreeQuotientCoordinate 1 F.V e).pair = A.k := by
    change e 0 + e 1 = A.k
    exact (A.coordinates e he).1
  rw [hpair] at hinterp
  have hkpos : 1 ≤ A.k := A.k_pos
  have hkle : A.k ≤ F.highest.n := A.k_le_highest
  have hdecomp :
      F.highest.n - 1 =
        (F.highest.n - A.k) + (A.k - 1) := by
    omega
  have hmul :
      F.stationaryWeight * (F.highest.n - 1) =
        F.stationaryWeight * (F.highest.n - A.k) +
          F.stationaryWeight * (A.k - 1) := by
    rw [hdecomp, Nat.mul_add]
  have hcontact :
      (F.highest.n - 1) * order =
        F.stationaryWeight * (A.k - 1) := by
    simpa [QsOtherFacetPrLeftVContactFrontierData.stationaryWeight] using hinterp
  calc
    (F.highest.n - 1) * order =
        F.stationaryWeight * (A.k - 1) := hcontact
    _ = F.stationaryTotalDegree -
        F.stationaryWeight * F.stationaryIndex A.k := by
      unfold QsOtherFacetPrLeftVContactFrontierData.stationaryTotalDegree
        QsOtherFacetPrLeftVContactFrontierData.stationaryIndex
      rw [hmul]
      simp

/-- Every actual stationary index lies inside the finite weighted support
interval `m*r <= D`. -/
theorem stationaryIndex_mul_weight_le_totalDegree
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    {D : QsOtherFacetPrLeftVPlanarContactReesData F}
    {order : ℕ}
    (A : QsOtherFacetPrLeftVParameterAffineLayerData D order) :
    F.stationaryIndex A.k * F.stationaryWeight ≤
      F.stationaryTotalDegree := by
  have hkpos : 1 ≤ A.k := A.k_pos
  have hindex : F.highest.n - A.k ≤ F.highest.n - 1 := by
    omega
  have hmul := Nat.mul_le_mul_right F.stationaryWeight hindex
  unfold QsOtherFacetPrLeftVContactFrontierData.stationaryIndex
    QsOtherFacetPrLeftVContactFrontierData.stationaryTotalDegree at *
  simpa [Nat.mul_comm] using hmul

end QsOtherFacetPrLeftVParameterAffineLayerData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
