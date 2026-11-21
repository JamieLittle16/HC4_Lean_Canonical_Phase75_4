import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrLeadingTransverseSlice
import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# A19.R18.21: contact-Rees transport of exposed transverse slices

The maximal transverse slices selected from a raw longitudinal profile live in
the source coefficient ring.  The honest contact Rees records every source
monomial at the parameter deficit

    D - (transverseDegree + profileWeight * longitudinalDegree).

This module first freezes that statement for an arbitrary exact transverse
component at an arbitrary longitudinal index.  The leading-slice theorem is
then just the canonical specialization used by R18.21.  The same generic
transport is consumed by the next-highest slice module, avoiding a second copy
of the contact-grading proof.

No determinant, Schur, or terminal geometry is used here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

/-- Longitudinal coefficient of the honest contact family, retaining the three
transverse source variables and the family parameter. -/
noncomputable def QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalSlice
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) : MvPolynomial (Fin 3) (Polynomial K) :=
  (MvPolynomial.finSuccEquiv (Polynomial K) 3 P.contactFamily).coeff n

/-- Exact coefficient formula for an honest contact-family longitudinal slice.
This is the whole-family counterpart of the layer dictionary in A19.121. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalSlice_coeff
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n : ℕ) (m : Fin 3 →₀ ℕ) :
    MvPolynomial.coeff m (R.contactLongitudinalSlice n) =
      Polynomial.X ^
          (T.topFace.degree -
            (qsContactTransverseDegree m + P.profileWeight * n)) *
        Polynomial.C (MvPolynomial.coeff m (R.profile.coeff n)) := by
  have hprofile :
      MvPolynomial.coeff m (R.profile.coeff n) =
        MvPolynomial.coeff (m.cons n)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) := by
    rw [R.profile_eq, qsContactRawLongitudinalProfile,
      MvPolynomial.finSuccEquiv_coeff_coeff]
  unfold QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalSlice
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [QsOtherFacetContactQuadraticReesPackage.contactFamily]
  rw [reverseWeightedReesFamily_coeff]
  rw [qsIntegralContactWeight_cons, ← P.profileWeight_eq]
  by_cases hd :
      m.cons n ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support
  · rw [if_pos hd]
    rw [← hprofile]
  · rw [if_neg hd]
    have hsource :
        MvPolynomial.coeff (m.cons n)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    have hraw : MvPolynomial.coeff m (R.profile.coeff n) = 0 := by
      rw [hprofile, hsource]
    rw [hraw]
    simp

/-- **R18.21 generic exact-component transport.**  Taking a fixed transverse
weight component of a longitudinal source slice commutes with passage to the
honest contact family, up to the single contact parameter monomial prescribed
by the exact grade. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.contactLongitudinalSlice_initialForm
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (n t : ℕ) :
    HC4.Polynomial.initialForm
        qsContactTransverseIntegerWeight (t : ℤ)
        (R.contactLongitudinalSlice n) =
      MvPolynomial.C
          (Polynomial.X ^
            (T.topFace.degree - (t + P.profileWeight * n))) *
        MvPolynomial.map Polynomial.C
          (HC4.Polynomial.initialForm
            qsContactTransverseIntegerWeight (t : ℤ)
            (R.profile.coeff n)) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [HC4.Polynomial.coeff_initialForm,
    weight_qsContactTransverseIntegerWeight]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rw [R.contactLongitudinalSlice_coeff]
  by_cases hm : qsContactTransverseDegree m = t
  · have hweight :
        (qsContactTransverseDegree m : ℤ) = (t : ℤ) := by
      exact_mod_cast hm
    rw [if_pos hweight]
    rw [HC4.Polynomial.coeff_initialForm,
      weight_qsContactTransverseIntegerWeight, if_pos hweight]
    rw [hm]
  · have hweight :
        (qsContactTransverseDegree m : ℤ) ≠ (t : ℤ) := by
      exact_mod_cast hm
    rw [if_neg hweight]
    rw [HC4.Polynomial.coeff_initialForm,
      weight_qsContactTransverseIntegerWeight, if_neg hweight]
    simp

/-- **R18.21 uniform contact order on the leading transverse slice.**

After selecting the maximal transverse homogeneous component, every surviving
coefficient has the same contact deficit.  Therefore the corresponding exact
component of the honest contact-family leading longitudinal slice is a single
parameter monomial times the constant lift of the raw homogeneous slice. -/
theorem QsOtherFacetContactLeadingTransverseSliceData.contactLeadingSlice_initialForm
    {R : QsOtherFacetContactRawLongitudinalProfilePackage C P}
    (S : QsOtherFacetContactLeadingTransverseSliceData R) :
    HC4.Polynomial.initialForm
        qsContactTransverseIntegerWeight (S.transverseDegree : ℤ)
        (R.contactLongitudinalSlice R.profile.natDegree) =
      MvPolynomial.C
          (Polynomial.X ^
            (T.topFace.degree -
              (S.transverseDegree +
                P.profileWeight * R.profile.natDegree))) *
        MvPolynomial.map Polynomial.C S.slice := by
  rw [S.slice_eq]
  exact R.contactLongitudinalSlice_initialForm
    R.profile.natDegree S.transverseDegree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
