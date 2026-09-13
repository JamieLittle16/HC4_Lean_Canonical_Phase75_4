import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneQuotientInterpolationRight
import Mathlib.Tactic

/-!
# A19 whole-carrier staircase equations in the non-unit PR branch

Affine interpolation of the quotient carrier immediately gives the concrete
staircase equations.  In the left orientation write a quotient point as

    (k,r,s) = (e0+e1, e0+e2, V*e0+e3).

The locked point is `(1,ell+1,V(ell+1))` and the primitive highest point is
`(n,1,Vn)`.  Therefore every actual carrier monomial satisfies

    (n-1)(r-1) = ell(n-k),
    s = V(k+r-1).

The right orientation is obtained by swapping the two transverse quotient
coordinates.  These formulas are independent of the longitudinal position
inside a fixed quotient fibre; that dependence has already been quotiented
out.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- State-free arithmetic: affine interpolation between the left locked and
highest quotient points is equivalent to the staircase wall equation and the
monomial-curve equation. -/
theorem left_staircase_equations_of_affine_interpolation
    (V ell n : ℕ) (q : RankThreeQuotientCoordinate)
    (hn : 2 ≤ n)
    (hfirst :
      ((n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - ((ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) * (1 - ((ell : ℤ) + 1)))
    (hsecond :
      ((n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) -
            (V : ℤ) * ((ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) *
          ((V : ℤ) * (n : ℤ) - (V : ℤ) * ((ell : ℤ) + 1))) :
    ((n : ℤ) - 1) * ((q.firstTransverse : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (q.pair : ℤ)) ∧
      (q.secondTransverse : ℤ) =
        (V : ℤ) *
          ((q.pair : ℤ) + (q.firstTransverse : ℤ) - 1) := by
  have hwall :
      ((n : ℤ) - 1) * ((q.firstTransverse : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (q.pair : ℤ)) := by
    nlinarith [hfirst]
  have hfactor :
      ((n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) -
            (V : ℤ) *
              ((q.pair : ℤ) + (q.firstTransverse : ℤ) - 1)) = 0 := by
    linear_combination hsecond - (V : ℤ) * hfirst
  have hnz : (n : ℤ) - 1 ≠ 0 := by
    have : (1 : ℤ) < (n : ℤ) := by exact_mod_cast (show 1 < n by omega)
    omega
  have hcurve :
      (q.secondTransverse : ℤ) =
        (V : ℤ) *
          ((q.pair : ℤ) + (q.firstTransverse : ℤ) - 1) := by
    have hz := (mul_eq_zero.mp hfactor).resolve_left hnz
    linarith
  exact ⟨hwall, hcurve⟩

/-- Swapped arithmetic companion. -/
theorem right_staircase_equations_of_affine_interpolation
    (V ell n : ℕ) (q : RankThreeQuotientCoordinate)
    (hn : 2 ≤ n)
    (hfirst :
      ((n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) -
            (V : ℤ) * ((ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) *
          ((V : ℤ) * (n : ℤ) - (V : ℤ) * ((ell : ℤ) + 1)))
    (hsecond :
      ((n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - ((ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) * (1 - ((ell : ℤ) + 1))) :
    ((n : ℤ) - 1) * ((q.secondTransverse : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (q.pair : ℤ)) ∧
      (q.firstTransverse : ℤ) =
        (V : ℤ) *
          ((q.pair : ℤ) + (q.secondTransverse : ℤ) - 1) := by
  have hwall :
      ((n : ℤ) - 1) * ((q.secondTransverse : ℤ) - 1) =
        (ell : ℤ) * ((n : ℤ) - (q.pair : ℤ)) := by
    nlinarith [hsecond]
  have hfactor :
      ((n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) -
            (V : ℤ) *
              ((q.pair : ℤ) + (q.secondTransverse : ℤ) - 1)) = 0 := by
    linear_combination hfirst - (V : ℤ) * hsecond
  have hnz : (n : ℤ) - 1 ≠ 0 := by
    have : (1 : ℤ) < (n : ℤ) := by exact_mod_cast (show 1 < n by omega)
    omega
  have hcurve :
      (q.firstTransverse : ℤ) =
        (V : ℤ) *
          ((q.pair : ℤ) + (q.secondTransverse : ℤ) - 1) := by
    have hz := (mul_eq_zero.mp hfactor).resolve_left hnz
    linarith
  exact ⟨hwall, hcurve⟩

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Every actual support point in the left non-unit carrier obeys the exact
staircase equations in quotient coordinates. -/
theorem QsOtherFacetPrLeftVContactFrontierData.support_staircase_equations
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := rankThreeQuotientCoordinate 1 F.V e
    ((F.highest.n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - 1) =
        (F.locked.ell : ℤ) *
          ((F.highest.n : ℤ) - (q.pair : ℤ)) ∧
      (q.secondTransverse : ℤ) =
        (F.V : ℤ) *
          ((q.pair : ℤ) + (q.firstTransverse : ℤ) - 1) := by
  let q := rankThreeQuotientCoordinate 1 F.V e
  have hi := F.quotient_affine_interpolation hthree houtThree he
  dsimp only at hi
  have hfirst :
      ((F.highest.n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) * (1 - ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq] using hi.1
  have hsecond :
      ((F.highest.n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) -
            (F.V : ℤ) * ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) *
          ((F.V : ℤ) * (F.highest.n : ℤ) -
            (F.V : ℤ) * ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq, mul_comm] using hi.2
  exact left_staircase_equations_of_affine_interpolation
    F.V F.locked.ell F.highest.n q F.highest.n_two_le hfirst hsecond

/-- Every actual support point in the swapped non-unit carrier obeys the
corresponding staircase equations. -/
theorem QsOtherFacetPrRightVContactFrontierData.support_staircase_equations
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := rankThreeQuotientCoordinate F.V 1 e
    ((F.highest.n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - 1) =
        (F.locked.ell : ℤ) *
          ((F.highest.n : ℤ) - (q.pair : ℤ)) ∧
      (q.firstTransverse : ℤ) =
        (F.V : ℤ) *
          ((q.pair : ℤ) + (q.secondTransverse : ℤ) - 1) := by
  let q := rankThreeQuotientCoordinate F.V 1 e
  have hi := F.quotient_affine_interpolation hthree houtThree he
  dsimp only at hi
  have hfirst :
      ((F.highest.n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) -
            (F.V : ℤ) * ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) *
          ((F.V : ℤ) * (F.highest.n : ℤ) -
            (F.V : ℤ) * ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq, mul_comm] using hi.1
  have hsecond :
      ((F.highest.n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) * (1 - ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq] using hi.2
  exact right_staircase_equations_of_affine_interpolation
    F.V F.locked.ell F.highest.n q F.highest.n_two_le hfirst hsecond

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
