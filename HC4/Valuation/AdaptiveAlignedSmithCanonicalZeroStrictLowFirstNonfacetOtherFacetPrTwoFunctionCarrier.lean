import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrCarrierReconstruction
import HC4.Polynomial.TwoFunctionCarrierHessianRigidity
import Mathlib.Tactic

/-!
# A19 source-facing PR two-function carrier endpoint

The source/contact reconstruction and the state-free two-function Hessian
contradiction live on opposite sides of the final rank-three seam.  This file
provides the deliberately thin adapter between them.

A `QsOtherFacetPrTwoFunctionCarrierData` records exactly the data that the
remaining support reconstruction has to produce from the normalized planar
carrier:

* the non-unit quotient slope `V > 1`;
* a positive locked-ray endpoint exponent `ell`;
* the two nonzero source coefficients `a,b`;
* one-variable polynomials `P,Q`, with `Q` genuinely nonlinear in the sense
  needed by the Euler-Hessian calculation; and
* literal equality of the actual source-honest planar carrier with the
  concrete `twoFunctionCarrier`.

No clock is identified here.  Once this package exists, the already-verified
positive-defect carrier equation `hessianDeterminant carrier = 0` is enough to
invoke `twoFunctionCarrier_hessian_impossible` directly.
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

/-- The exact source-facing normal form required by the existing concrete
Euler-Hessian contradiction.  This is intentionally a data package rather
than a new mathematical hypothesis: the next reconstruction step builds it
from the normalized quotient carrier and literal source coefficients. -/
structure QsOtherFacetPrTwoFunctionCarrierData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr) where
  V : ℕ
  ell : ℕ
  V_gt_one : 1 < V
  ell_pos : 0 < ell
  a : K
  b : K
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  Ppoly : Polynomial K
  Qpoly : Polynomial K
  Qpoly_derivative_ne : Qpoly.derivative ≠ 0
  carrier_eq :
    P.carrier =
      HC4.Polynomial.twoFunctionCarrier V ell a b Ppoly Qpoly

namespace QsOtherFacetPrTwoFunctionCarrierData

/-- The non-unit quotient parameter is in particular positive. -/
theorem V_pos
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (D : QsOtherFacetPrTwoFunctionCarrierData C P) :
    0 < D.V := by
  omega

/-- **Standard non-unit PR carrier endpoint.**  Once source reconstruction has
produced the literal two-function carrier package, the branch is impossible.
All Hessian algebra is delegated to the existing state-free theorem. -/
theorem impossible
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (D : QsOtherFacetPrTwoFunctionCarrierData C P) :
    False := by
  apply HC4.Polynomial.twoFunctionCarrier_hessian_impossible
    D.V D.ell D.V_pos D.ell_pos
    D.a D.b D.a_ne D.b_ne
    D.Ppoly D.Qpoly D.Qpoly_derivative_ne
  rw [← D.carrier_eq]
  exact P.hessian_zero

end QsOtherFacetPrTwoFunctionCarrierData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
