import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneContactSeparation
import Mathlib.Tactic

/-!
# A19 non-unit PR wall/contact interpolation

The retained source wall and the honest contact grading use the same two
endpoint packages, but they measure an intermediate staircase point in two
different ways.  This file records the elementary arithmetic bridge once.

If a left/right primitive candidate at pair degree `k` and `H`-height `j`
satisfies

    (n - 1) * j = ell * (n - k),

then its contact deficit from the locked top degree is governed by

    (n - 1) * (ell + 1 - k - j)
      = (ell + 1 - n) * (k - 1).

The source contact bound supplies the nonnegativity of `ell + 1 - k - j` for
an actual carrier monomial.  No Rees clock is identified with the blocker or
ray clock here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- State-free interpolation identity obtained from the wall-slope equation. -/
theorem prVGreaterOne_wallSlope_contactDeficit_identity
    (ell n k j : ℕ)
    (hslope :
      ((n : ℤ) - 1) * (j : ℤ) =
        (ell : ℤ) * ((n : ℤ) - (k : ℤ))) :
    ((n : ℤ) - 1) *
        ((ell : ℤ) + 1 - (k : ℤ) - (j : ℤ)) =
      ((ell : ℤ) + 1 - (n : ℤ)) * ((k : ℤ) - 1) := by
  nlinarith

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- An actual left-oriented staircase monomial lies weakly below the locked
contact top: `k+j <= ell+1`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.staircase_contact_bound
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
    k + j ≤ F.locked.ell + 1 := by
  have hsource := P.support_source he
  have hbound := R.source_weight_le hsource
  rw [F.topFace_degree_eq] at hbound
  rw [HC4.Polynomial.ordinaryDegree4, he0, he1, he2, he3] at hbound
  simp only [Nat.zero_add, Nat.mul_zero, add_zero] at hbound
  nlinarith [F.V_gt_one]

/-- Symmetric contact-top bound in the `(V,1)` orientation. -/
theorem QsOtherFacetPrRightVContactFrontierData.staircase_contact_bound
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
    k + j ≤ F.locked.ell + 1 := by
  have hsource := P.support_source he
  have hbound := R.source_weight_le hsource
  rw [F.topFace_degree_eq] at hbound
  rw [HC4.Polynomial.ordinaryDegree4, he0, he1, he2, he3] at hbound
  simp only [Nat.zero_add, Nat.mul_zero, add_zero] at hbound
  nlinarith [F.V_gt_one]

/-- The wall slope and honest contact deficit interpolate linearly between the
locked endpoint (`k=1`) and the primitive highest endpoint (`k=n`). -/
theorem QsOtherFacetPrLeftVContactFrontierData.wallSlope_contactDeficit_identity
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
    ((F.highest.n : ℤ) - 1) *
        ((F.locked.ell : ℤ) + 1 - (k : ℤ) - (j : ℤ)) =
      ((F.locked.ell : ℤ) + 1 - (F.highest.n : ℤ)) *
        ((k : ℤ) - 1) := by
  exact prVGreaterOne_wallSlope_contactDeficit_identity
    F.locked.ell F.highest.n k j
    (F.wallSlope_eq he he0 he1 he2 he3)

/-- Symmetric interpolation identity for `(V,1)`. -/
theorem QsOtherFacetPrRightVContactFrontierData.wallSlope_contactDeficit_identity
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
    ((F.highest.n : ℤ) - 1) *
        ((F.locked.ell : ℤ) + 1 - (k : ℤ) - (j : ℤ)) =
      ((F.locked.ell : ℤ) + 1 - (F.highest.n : ℤ)) *
        ((k : ℤ) - 1) := by
  exact prVGreaterOne_wallSlope_contactDeficit_identity
    F.locked.ell F.highest.n k j
    (F.wallSlope_eq he he0 he1 he2 he3)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
