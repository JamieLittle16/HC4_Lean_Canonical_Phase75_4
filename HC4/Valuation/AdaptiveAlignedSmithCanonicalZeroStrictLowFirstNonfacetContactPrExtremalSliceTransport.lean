import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrLeadingSliceTransport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalSlices
import Mathlib.Tactic

/-!
# A19.R18.23: contact transport of the next exposed PR slice

The generic exact-component transport in R18.21 already handles every
longitudinal index.  This module merely specializes it to the next-highest
profile coefficient retained by `QsOtherFacetContactNextTransverseSliceData`.
There is no second contact-grading argument here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

/-- **R18.23 next-highest slice transport.**  The retained maximal transverse
component at longitudinal degree `M` occurs in the honest contact family at one
exact parameter deficit. -/
theorem QsOtherFacetContactNextTransverseSliceData.contactNextSlice_initialForm
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactNextTransverseSliceData R) :
    HC4.Polynomial.initialForm
        qsContactTransverseIntegerWeight (S.transverseDegree : ℤ)
        (R.contactLongitudinalSlice S.M) =
      MvPolynomial.C
          (Polynomial.X ^
            (T.topFace.degree -
              (S.transverseDegree + P.profileWeight * S.M))) *
        MvPolynomial.map Polynomial.C S.slice := by
  rw [S.slice_eq]
  exact R.contactLongitudinalSlice_initialForm S.M S.transverseDegree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
