import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrContactSlope
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLayerGrading
import Mathlib.Tactic

/-!
# A19 contact grading on the normalized PR planar carrier

The normalized locked direction and the integral contact slope are compatible
in a particularly rigid way.  For direction `(1,-1,-alpha,-beta)` the contact
slope is `alpha+beta`, hence

    ordinaryDegree4 e + (alpha+beta) * e₀
      = (e₀+e₁) + (alpha*e₀+e₂) + (beta*e₀+e₃).

The right hand side is simply the sum of the three rank-three quotient
coordinates.  Thus the actual contact-Rees order factors through the *same*
quotient point already controlled by the two retained planar equations.

This file also records literal source provenance for every planar-carrier
monomial inside the canonical contact family.  No support point is recreated:
the coefficient in its exact contact layer is definitionally the original
represented-source coefficient and is nonzero.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Elementary quotient identity behind the contact grading. -/
theorem ordinaryDegree4_add_quotientDrops_mul_zero
    (alpha beta : ℕ) (e : Fin 4 →₀ ℕ) :
    HC4.Polynomial.ordinaryDegree4 e + (alpha + beta) * e 0 =
      (rankThreeQuotientCoordinate alpha beta e).pair +
        (rankThreeQuotientCoordinate alpha beta e).firstTransverse +
        (rankThreeQuotientCoordinate alpha beta e).secondTransverse := by
  simp [HC4.Polynomial.ordinaryDegree4, rankThreeQuotientCoordinate]
  omega

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Every planar-carrier support exponent is literally support of the
represented zero-clock source. -/
theorem QsOtherFacetPlanarCarrierPackage.support_source
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    e ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support := by
  have hface := HC4.Newton.initialForm_support_isExposedFace
    P.finalWeight P.finalLevel
    (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    P.source_bound
  have hi : e ∈
      (HC4.Polynomial.initialForm P.finalWeight P.finalLevel
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)).support := by
    simpa [P.carrier_eq_initialForm] using he
  exact (hface.mem_iff.mp (by simpa using hi)).1

/-- The contact gap stored by the canonical contact-Rees package is exactly the
sum of the two normalized transverse quotient drops.  The proof compares the
two independently source-honest integral contact constructions through their
common positive scale; no filtration clocks are identified. -/
theorem QsOtherFacetPrQuotientCarrierData.contactGap_eq_sum
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    R.contactGap = alpha + beta := by
  rcases C.qs_ray_pr_integral_source_contact hthree houtThree with
    ⟨r, _hr, hbump, _hsource, hray⟩
  have hsame : R.contactGap = r := by
    have hmul : C.scale * R.contactGap = C.scale * r := by
      rw [← R.bump_eq, ← hbump]
    exact Nat.mul_left_cancel hmul
  have hrsum : r = alpha + beta := Q.contactSlope_eq_sum hray
  exact hsame.trans hrsum

/-- On every exponent, the canonical contact source weight is the sum of the
three normalized quotient coordinates. -/
theorem QsOtherFacetPrQuotientCarrierData.contactWeight_eq_quotientSum
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (e : Fin 4 →₀ ℕ) :
    HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0 =
      (rankThreeQuotientCoordinate alpha beta e).pair +
        (rankThreeQuotientCoordinate alpha beta e).firstTransverse +
        (rankThreeQuotientCoordinate alpha beta e).secondTransverse := by
  rw [Q.contactGap_eq_sum R hthree houtThree]
  exact ordinaryDegree4_add_quotientDrops_mul_zero alpha beta e

/-- Hence quotient-equal source exponents have exactly the same integral
contact weight. -/
theorem QsOtherFacetPrQuotientCarrierData.contactWeight_eq_of_quotient_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f) :
    HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0 =
      HC4.Polynomial.ordinaryDegree4 f + R.contactGap * f 0 := by
  rw [Q.contactWeight_eq_quotientSum R hthree houtThree e,
    Q.contactWeight_eq_quotientSum R hthree houtThree f, hq]

/-- A literal planar-carrier coefficient appears unchanged and nontrivially in
its exact canonical contact-Rees layer. -/
theorem QsOtherFacetPlanarCarrierPackage.contactFamily_coeff_at_source_deficit
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {next : ToricFacet}
    (P : QsOtherFacetPlanarCarrierPackage C next)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    MvPolynomial.coeff e
        (familyParameterLayer R.contactFamily
          (T.topFace.degree -
            (HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0))) =
      MvPolynomial.coeff e
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ∧
    MvPolynomial.coeff e
        (familyParameterLayer R.contactFamily
          (T.topFace.degree -
            (HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0))) ≠ 0 := by
  have hsource : e ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support := P.support_source he
  have heq := R.contactFamily_source_coeff_at_deficit hsource
  have hne : MvPolynomial.coeff e
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hsource
  exact ⟨heq, heq.trans_ne hne⟩

/-- Two actual planar-carrier monomials in one quotient fiber occur in the same
canonical contact-Rees layer. -/
theorem QsOtherFacetPrQuotientCarrierData.contactOrder_eq_of_quotient_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {alpha beta : ℕ}
    (Q : QsOtherFacetPrQuotientCarrierData C P alpha beta)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e f : Fin 4 →₀ ℕ}
    (hq : rankThreeQuotientCoordinate alpha beta e =
      rankThreeQuotientCoordinate alpha beta f) :
    T.topFace.degree -
        (HC4.Polynomial.ordinaryDegree4 e + R.contactGap * e 0) =
      T.topFace.degree -
        (HC4.Polynomial.ordinaryDegree4 f + R.contactGap * f 0) := by
  rw [Q.contactWeight_eq_of_quotient_eq R hthree houtThree hq]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
