import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFourTermCarrier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrTwoFunctionCarrier
import HC4.Polynomial.TwoFunctionCarrierMonomialNormalForm
import Mathlib.Tactic

/-!
# A19 exact two-function reconstruction after interior elimination

The geometric content of the standard non-unit branch is now isolated in
`NoStrictInteriorSupport`.  Once that proposition is available, the carrier is
already a literal four-term source polynomial.  This file performs only the
remaining normalization into

    x (Q(Y) + b H^ell) + z (P(Y) + a H^ell Y),
    Y = y w^V,  H = z w^V.

The one-variable polynomials are single monomials supplied by the primitive
highest pair.  Their coefficients are the literal carrier/source
coefficients, so no division or coefficient recreation occurs.
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

/-- The locked facet exponent is exactly the `z H^ell Y` exponent. -/
theorem QsOtherFacetPrLeftVContactFrontierData.locked_facet_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    C.ray.facetExponent =
      HC4.Polynomial.twoFunctionLockedFacetExponent F.V F.locked.ell := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionLockedFacetExponent,
      HC4.Polynomial.twoFunctionHExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three] <;> ring

/-- The locked outside exponent is exactly the `x H^ell` exponent. -/
theorem QsOtherFacetPrLeftVContactFrontierData.locked_outside_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    C.ray.outsideExponent =
      HC4.Polynomial.twoFunctionLockedOutsideExponent F.V F.locked.ell := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionLockedOutsideExponent,
      HC4.Polynomial.twoFunctionHExponent,
      F.locked.outside_zero, F.locked.outside_one,
      F.locked.outside_two, F.locked.outside_three] <;> ring

/-- The coordinate-zero layer of the primitive highest pair is `z Y^n`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.highest_e0_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    F.highest.e0 =
      HC4.Polynomial.twoFunctionHighestZExponent F.V F.highest.n := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionHighestZExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq] <;> ring

/-- The coordinate-one layer of the primitive highest pair is `x Y^(n-1)`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.highest_e1_eq_twoFunctionExponent
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) :
    F.highest.e1 =
      HC4.Polynomial.twoFunctionHighestXExponent F.V F.highest.n := by
  ext i
  fin_cases i <;>
    simp [HC4.Polynomial.twoFunctionHighestXExponent,
      HC4.Polynomial.twoFunctionYExponent,
      F.highest.e1_zero, F.highest.e1_one,
      F.highest.e1_two, F.highest.e1_three,
      F.highest_V_eq] <;> ring

/-- **Exact standard-branch reconstruction.**  After strict-interior support is
eliminated, the actual source-honest carrier produces the precise data package
consumed by the already-verified two-function Hessian contradiction. -/
theorem QsOtherFacetPrLeftVContactFrontierData.twoFunctionCarrierData_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) :
    Nonempty (QsOtherFacetPrTwoFunctionCarrierData C P) := by
  rcases F.fourTermCarrierData_of_noStrictInterior hno with ⟨D⟩
  let Ppoly : Polynomial K := Polynomial.monomial F.highest.n D.p
  let Qpoly : Polynomial K := Polynomial.monomial (F.highest.n - 1) D.q
  have hn1 : F.highest.n - 1 ≠ 0 := by omega
  have hQderiv : Qpoly.derivative ≠ 0 := by
    dsimp [Qpoly]
    rw [Polynomial.derivative_monomial]
    rw [Polynomial.monomial_eq_zero_iff]
    exact mul_ne_zero D.q_ne ((Nat.cast_ne_zero).2 hn1)
  have hcarrier :
      P.carrier =
        HC4.Polynomial.twoFunctionCarrier
          F.V F.locked.ell D.a D.b Ppoly Qpoly := by
    calc
      P.carrier =
          MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionLockedFacetExponent
                F.V F.locked.ell) D.a +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionLockedOutsideExponent
                F.V F.locked.ell) D.b +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionHighestZExponent
                F.V F.highest.n) D.p +
            MvPolynomial.monomial
              (HC4.Polynomial.twoFunctionHighestXExponent
                F.V F.highest.n) D.q := by
          rw [D.carrier_eq,
            F.locked_facet_eq_twoFunctionExponent,
            F.locked_outside_eq_twoFunctionExponent,
            F.highest_e0_eq_twoFunctionExponent,
            F.highest_e1_eq_twoFunctionExponent]
      _ = HC4.Polynomial.twoFunctionCarrier
          F.V F.locked.ell D.a D.b Ppoly Qpoly := by
        symm
        simpa [Ppoly, Qpoly] using
          (HC4.Polynomial.twoFunctionCarrier_monomial_normalForm
            (K := K) F.V F.locked.ell F.highest.n D.a D.b D.p D.q)
  exact ⟨{
    V := F.V
    ell := F.locked.ell
    V_gt_one := F.V_gt_one
    ell_pos := F.locked.ell_pos
    a := D.a
    b := D.b
    a_ne := D.a_ne
    b_ne := D.b_ne
    Ppoly := Ppoly
    Qpoly := Qpoly
    Qpoly_derivative_ne := hQderiv
    carrier_eq := hcarrier
  }⟩

/-- Once the single `NoStrictInteriorSupport` obligation is discharged, the
left `V>1` branch closes immediately by the existing Hessian rigidity theorem. -/
theorem QsOtherFacetPrLeftVContactFrontierData.impossible_of_noStrictInterior
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hno : F.NoStrictInteriorSupport) : False := by
  rcases F.twoFunctionCarrierData_of_noStrictInterior hno with ⟨D⟩
  exact D.impossible

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
