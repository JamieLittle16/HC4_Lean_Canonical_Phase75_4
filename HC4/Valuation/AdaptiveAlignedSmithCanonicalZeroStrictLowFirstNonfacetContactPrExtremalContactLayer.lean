import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalOrders
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLayerGrading
import HC4.Polynomial.WeightedInitial
import Mathlib.Tactic

/-!
# A19.R18.29: exact honest-contact layers of the two exposed PR slices

The qNN/qNM coefficient calculation should not manipulate coefficient-ring
parameter derivatives and transverse source grading at the same time.  The
honest contact Rees already separates them exactly.

For longitudinal index `n`, contact parameter order `q`, and transverse degree
`t` satisfying

    q + profileWeight * n + t = D,

the longitudinal coefficient of the exact contact parameter layer `q` is
literally the transverse weight-`t` component of the raw longitudinal profile
coefficient.  This file records that dictionary once and specializes it to the
leading and next-highest slices retained by `prExtremalDegreeData`.

No determinant, Schur identity, pivot cancellation, or terminal vanishing is
used here.  The next coefficient calculation can therefore work entirely with
the two nonzero source polynomials `E.leading.slice` and `E.next.slice`.
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

/-- Exact parameter layer `q` of the honest contact family, followed by the
longitudinal coefficient `n`.  The result retains only the three transverse
source variables. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n : ℕ) : MvPolynomial (Fin 3) K :=
  (MvPolynomial.finSuccEquiv K 3
    (familyParameterLayer P.contactFamily q)).coeff n

/-- **R18.29 exact contact-layer dictionary.**  At a fixed honest contact
grade, parameter-layer extraction and longitudinal coefficient extraction leave
exactly the matching transverse homogeneous component of the raw profile. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer_eq_initialForm
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (q n t : ℕ)
    (hgrade : q + P.profileWeight * n + t = T.topFace.degree) :
    R.contactLongitudinalParameterLayer q n =
      HC4.Polynomial.initialForm
        qsContactTransverseIntegerWeight (t : ℤ) (R.profile.coeff n) := by
  classical
  apply MvPolynomial.ext
  intro m
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalParameterLayer
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [P.contactFamily_longitudinal_transverse_coeff q n m]
  rw [← R.profile_eq]
  rw [HC4.Polynomial.coeff_initialForm,
    weight_qsContactTransverseIntegerWeight]
  by_cases hm : MvPolynomial.coeff m (R.profile.coeff n) = 0
  · split <;> simp [hm]
  · have hmne : MvPolynomial.coeff m (R.profile.coeff n) ≠ 0 := hm
    have hmSupport : m ∈ (R.profile.coeff n).support :=
      MvPolynomial.mem_support_iff.mpr hmne
    have hsourceCoeff := hmne
    rw [R.profile_eq, qsContactRawLongitudinalProfile,
      MvPolynomial.finSuccEquiv_coeff_coeff] at hsourceCoeff
    have hsource :
        m.cons n ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support :=
      MvPolynomial.mem_support_iff.mpr hsourceCoeff
    have hbound := R.transverseDegree_add_profileWeight_mul_le hmSupport
    by_cases hmt : qsContactTransverseDegree m = t
    · have hweight :
          (qsContactTransverseDegree m : ℤ) = (t : ℤ) := by
        exact_mod_cast hmt
      have hq :
          T.topFace.degree -
              (qsContactTransverseDegree m + P.profileWeight * n) = q := by
        rw [hmt]
        omega
      rw [if_pos ⟨hsource, hq⟩, if_pos hweight]
    · have hweight :
          (qsContactTransverseDegree m : ℤ) ≠ (t : ℤ) := by
        exact_mod_cast hmt
      have hqne :
          T.topFace.degree -
              (qsContactTransverseDegree m + P.profileWeight * n) ≠ q := by
        intro hq
        omega
      rw [if_neg, if_neg hweight]
      intro hcond
      exact hqne hcond.2

/-- The first exposed contact layer is literally the retained nonzero leading
transverse slice. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactLeadingParameterLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    R.contactLongitudinalParameterLayer E.qN E.next.N = E.leading.slice := by
  calc
    R.contactLongitudinalParameterLayer E.qN E.next.N =
        HC4.Polynomial.initialForm
          qsContactTransverseIntegerWeight
          (E.leading.transverseDegree : ℤ)
          (R.profile.coeff E.next.N) :=
      R.contactLongitudinalParameterLayer_eq_initialForm
        E.qN E.next.N E.leading.transverseDegree E.leading_grade
    _ = E.leading.slice := by
      rw [E.next.N_eq]
      exact E.leading.slice_eq.symm

/-- The second exposed contact layer is literally the retained nonzero
next-highest transverse slice. -/
theorem QsOtherFacetContactPrExtremalDegreeData.contactNextParameterLayer_eq
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (E : QsOtherFacetContactPrExtremalDegreeData R) :
    R.contactLongitudinalParameterLayer E.qM E.next.M = E.next.slice := by
  calc
    R.contactLongitudinalParameterLayer E.qM E.next.M =
        HC4.Polynomial.initialForm
          qsContactTransverseIntegerWeight
          (E.next.transverseDegree : ℤ)
          (R.profile.coeff E.next.M) :=
      R.contactLongitudinalParameterLayer_eq_initialForm
        E.qM E.next.M E.next.transverseDegree E.next_grade
    _ = E.next.slice := E.next.slice_eq.symm

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
