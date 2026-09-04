import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrLeadingTransverseSlice
import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# A19.R18.21: contact-Rees transport of the leading transverse slice

The maximal transverse slice selected in the previous module lives in the raw
source profile.  The honest contact Rees records every source monomial at the
parameter deficit

    D - (transverseDegree + profileWeight * longitudinalDegree).

This module freezes that statement first for an arbitrary longitudinal slice,
then for the leading maximal-transverse homogeneous component.  On that
component the transverse degree is constant, so the whole component is
literally one parameter monomial times the raw homogeneous slice.

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

/-- **R18.21 uniform contact order on the leading transverse slice.**

After selecting the maximal transverse homogeneous component, every surviving
coefficient has the same contact deficit.  Therefore the corresponding exact
component of the honest contact-family leading longitudinal slice is a single
parameter monomial times the constant lift of the raw slice. -/
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
  classical
  apply MvPolynomial.ext
  intro m
  rw [HC4.Polynomial.coeff_initialForm,
    weight_qsContactTransverseIntegerWeight]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rw [R.contactLongitudinalSlice_coeff]
  by_cases hm : qsContactTransverseDegree m = S.transverseDegree
  · have hweight :
        (qsContactTransverseDegree m : ℤ) =
          (S.transverseDegree : ℤ) := by exact_mod_cast hm
    rw [if_pos hweight]
    have hScoeff :
        MvPolynomial.coeff m S.slice =
          MvPolynomial.coeff m
            (R.profile.coeff R.profile.natDegree) := by
      rw [S.slice_eq, HC4.Polynomial.coeff_initialForm,
        weight_qsContactTransverseIntegerWeight, if_pos hweight]
    rw [hScoeff, hm]
  · have hweight :
        (qsContactTransverseDegree m : ℤ) ≠
          (S.transverseDegree : ℤ) := by exact_mod_cast hm
    rw [if_neg hweight]
    have hSzero : MvPolynomial.coeff m S.slice = 0 := by
      rw [S.slice_eq, HC4.Polynomial.coeff_initialForm,
        weight_qsContactTransverseIntegerWeight, if_neg hweight]
    rw [hSzero]
    simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
