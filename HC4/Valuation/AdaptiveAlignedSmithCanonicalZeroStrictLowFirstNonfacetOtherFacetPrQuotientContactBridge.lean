import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrCarrierReconstruction
import Mathlib.Tactic

/-!
# A19 normalized PR quotient coordinates in the honest contact filtration

The normalized planar carrier and the canonical contact Rees are both attached
to the same represented source, but they encode an exponent differently.
For direction `(1,-1,-alpha,-beta)` the source contact weight is exactly the
sum of the three quotient coordinates.  Hence the honest contact parameter
order of a planar-carrier monomial is determined directly by its normalized
quotient point.

This file records that dictionary once.  In particular, two actual carrier
monomials in one fixed `.pr` pair-degree fibre have the same quotient point and
therefore occur in the same exact contact parameter layer, with both literal
source coefficients nonzero.

No filtration clocks are identified: the equalities below are consequences of
`contactGap_eq_sum` and the source coefficient formula already proved for the
canonical contact family.
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

/-- Contact parameter deficit written purely in normalized quotient
coordinates. -/
def qsOtherFacetPrQuotientContactOrder
    (alpha beta : ℕ) (e : Fin 4 →₀ ℕ) : ℕ :=
  T.topFace.degree -
    ((rankThreeQuotientCoordinate alpha beta e).pair +
      (rankThreeQuotientCoordinate alpha beta e).firstTransverse +
      (rankThreeQuotientCoordinate alpha beta e).secondTransverse)

/-- The quotient-coordinate order is exactly the honest source contact
deficit. -/
theorem QsOtherFacetPrQuotientCarrierData.sourceContactDeficit_eq_quotientContactOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (e : Fin 4 →₀ ℕ) :
    T.topFace.degree -
        (HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0) =
      qsOtherFacetPrQuotientContactOrder (T := T) alpha beta e := by
  unfold qsOtherFacetPrQuotientContactOrder
  rw [Q.contactWeight_eq_quotientSum R hthree houtThree e]

/-- A literal carrier coefficient appears unchanged and nontrivially at the
contact order read from its normalized quotient point. -/
theorem QsOtherFacetPlanarCarrierPackage.contactFamily_coeff_at_quotientContactOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    MvPolynomial.coeff e
        (familyParameterLayer R.contactFamily
          (qsOtherFacetPrQuotientContactOrder (T := T) alpha beta e)) =
      MvPolynomial.coeff e
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family) ∧
    MvPolynomial.coeff e
        (familyParameterLayer R.contactFamily
          (qsOtherFacetPrQuotientContactOrder (T := T) alpha beta e)) ≠ 0 := by
  have h := P.contactFamily_coeff_at_source_deficit R he
  have horder := Q.sourceContactDeficit_eq_quotientContactOrder
    R hthree houtThree e
  rw [horder] at h
  exact h

/-- Equal pair degree on two actual carrier monomials means equal exact
contact order.  This is the type-safe bridge used by the forthcoming
contact-aware fibre classification. -/
theorem QsOtherFacetPrQuotientCarrierData.quotientContactOrder_eq_of_pairDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair : qsOtherFacetPairDegree .pr e = qsOtherFacetPairDegree .pr f) :
    qsOtherFacetPrQuotientContactOrder (T := T) alpha beta e =
      qsOtherFacetPrQuotientContactOrder (T := T) alpha beta f := by
  have hq := Q.pair_fiber he hf hpair
  unfold qsOtherFacetPrQuotientContactOrder
  rw [hq]

/-- Consequently a two-monomial carrier fibre is represented by two nonzero
source coefficients in one and the same exact contact parameter layer. -/
theorem QsOtherFacetPrQuotientCarrierData.pairFiber_contact_coefficients_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair : qsOtherFacetPairDegree .pr e = qsOtherFacetPairDegree .pr f) :
    let q := qsOtherFacetPrQuotientContactOrder (T := T) alpha beta e
    MvPolynomial.coeff e (familyParameterLayer R.contactFamily q) ≠ 0 ∧
      MvPolynomial.coeff f (familyParameterLayer R.contactFamily q) ≠ 0 := by
  let q := qsOtherFacetPrQuotientContactOrder (T := T) alpha beta e
  have heq := P.contactFamily_coeff_at_quotientContactOrder
    Q R hthree houtThree he
  have hfq := P.contactFamily_coeff_at_quotientContactOrder
    Q R hthree houtThree hf
  have horder := Q.quotientContactOrder_eq_of_pairDegree_eq he hf hpair
  dsimp [q]
  refine ⟨heq.2, ?_⟩
  rw [horder]
  exact hfq.2

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
