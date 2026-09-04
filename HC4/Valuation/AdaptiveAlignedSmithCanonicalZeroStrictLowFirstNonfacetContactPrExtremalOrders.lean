import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalSlices
import Mathlib.Tactic

/-!
# A19.R18.26: exact parameter orders of the two exposed PR pairs

The contact and binary filtrations are deliberately not identified.  For the
two extremal longitudinal pairs we only need their exact arithmetic relation.
If the leading slice has contact deficit `qN` and transverse degree `t`, then

    qNN = 2D - r(2N) = qN + qN + t + t.

For the leading/next pair, with next deficit `qM` and transverse degree `u`,

    qNM = 2D - r(N+M) = qN + qM + t + u.

These are consequences only of the two honest contact grading equations
retained by `QsOtherFacetContactPrExtremalDegreeData`.  They are the exact
bookkeeping needed by the coefficientwise transverse-inflation transport.
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
variable {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}

/-- **R18.26 leading-pair order.** -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNN_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.N) =
      E.qN + E.qN +
        E.leading.transverseDegree + E.leading.transverseDegree := by
  have h := E.leading_grade
  rw [Nat.mul_add]
  omega

/-- **R18.26 leading/next-pair order.** -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNM_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.M) =
      E.qN + E.qM +
        E.leading.transverseDegree + E.next.transverseDegree := by
  have hN := E.leading_grade
  have hM := E.next_grade
  rw [Nat.mul_add]
  omega

/-- The binary active-pivot order is the leading contact-pair order plus the
four transverse powers contributed by the active two-by-two Hessian pivot. -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNN_add_four_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.N)) + 4 =
      E.qN + E.qN +
        (E.leading.transverseDegree + E.leading.transverseDegree + 4) := by
  rw [E.qNN_eq_contact_pair]
  omega

/-- Likewise for the leading/next pair. -/
theorem QsOtherFacetContactPrExtremalDegreeData.qNM_add_four_eq_contact_pair
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    (2 * T.topFace.degree -
        P.profileWeight * (E.next.N + E.next.M)) + 4 =
      E.qN + E.qM +
        (E.leading.transverseDegree + E.next.transverseDegree + 4) := by
  rw [E.qNM_eq_contact_pair]
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
