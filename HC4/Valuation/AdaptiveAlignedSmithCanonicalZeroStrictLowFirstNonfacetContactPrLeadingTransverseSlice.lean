import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactPrExtremalScalar
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLayerGrading
import HC4.Polynomial.WeightedInitial
import Mathlib.Tactic

/-!
# A19.R18.21: maximal transverse slice of the leading profile coefficient

The PR extremal scalar is uniform only after fixing the total transverse
degree.  Rather than choose a monomial order, we reuse the repository's exact
weighted-component machinery.

For the leading longitudinal coefficient

    A_N = profile.coeff profile.natDegree,

choose a supported transverse exponent of maximal total degree `t`, and take
the exact weight-`t` component for the all-ones transverse weight.  The
resulting slice is nonzero, is homogeneous of exact transverse degree `t`, and
retains only genuine coefficients of `A_N`.

This is finite-support bookkeeping.  It introduces no Schur identity,
vanishing statement, endpoint extrapolation, or new termination measure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- All-ones integer weight on the three transverse profile variables. -/
def qsContactTransverseIntegerWeight : Fin 3 → ℤ := fun _ => 1

/-- Its Finsupp weight is exactly the existing contact transverse degree. -/
theorem weight_qsContactTransverseIntegerWeight
    (m : Fin 3 →₀ ℕ) :
    Finsupp.weight qsContactTransverseIntegerWeight m =
      (qsContactTransverseDegree m : ℤ) := by
  rw [Finsupp.weight_apply]
  simp [qsContactTransverseIntegerWeight, Finsupp.sum_fintype,
    qsContactTransverseDegree, Fin.sum_univ_three]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}
variable {P : QsOtherFacetContactQuadraticReesPackage C}

/-- Canonical maximal-transverse homogeneous piece of the leading longitudinal
profile coefficient. -/
structure QsOtherFacetContactLeadingTransverseSliceData
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) where
  transverseDegree : ℕ
  slice : MvPolynomial (Fin 3) K
  slice_eq :
    slice = HC4.Polynomial.initialForm
      qsContactTransverseIntegerWeight (transverseDegree : ℤ)
      (R.profile.coeff R.profile.natDegree)
  slice_ne_zero : slice ≠ 0
  slice_homogeneous :
    MvPolynomial.IsWeightedHomogeneous
      qsContactTransverseIntegerWeight slice (transverseDegree : ℤ)
  slice_source :
    ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m slice ≠ 0 →
        MvPolynomial.coeff m
          (R.profile.coeff R.profile.natDegree) ≠ 0
  slice_exact_transverseDegree :
    ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m slice ≠ 0 →
        qsContactTransverseDegree m = transverseDegree
  transverseDegree_max :
    ∀ m : Fin 3 →₀ ℕ,
      MvPolynomial.coeff m
          (R.profile.coeff R.profile.natDegree) ≠ 0 →
        qsContactTransverseDegree m ≤ transverseDegree

/-- **R18.21 leading transverse slice.**  The nonzero leading longitudinal
coefficient always has a nonzero maximal transverse homogeneous component. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.exists_leadingTransverseSlice
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P) :
    Nonempty (QsOtherFacetContactLeadingTransverseSliceData R) := by
  classical
  let A : MvPolynomial (Fin 3) K :=
    R.profile.coeff R.profile.natDegree
  have hprofile : R.profile ≠ 0 := by
    intro hzero
    have hdeg := R.degree_two_le
    rw [hzero] at hdeg
    simp at hdeg
  have hAne : A ≠ 0 := by
    dsimp [A]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hprofile
  have hAsupport : A.support.Nonempty := MvPolynomial.support_nonempty.mpr hAne
  rcases Finset.exists_max_image A.support qsContactTransverseDegree hAsupport with
    ⟨m, hmA, hmax⟩
  let t : ℕ := qsContactTransverseDegree m
  let S : MvPolynomial (Fin 3) K :=
    HC4.Polynomial.initialForm
      qsContactTransverseIntegerWeight (t : ℤ) A
  have hmcoeff : MvPolynomial.coeff m A ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmA
  have hmweight :
      Finsupp.weight qsContactTransverseIntegerWeight m = (t : ℤ) := by
    rw [weight_qsContactTransverseIntegerWeight]
  have hmS : MvPolynomial.coeff m S ≠ 0 := by
    dsimp [S]
    rw [HC4.Polynomial.coeff_initialForm, if_pos hmweight]
    exact hmcoeff
  have hSne : S ≠ 0 := by
    intro hzero
    rw [hzero] at hmS
    simp at hmS
  have hShom :
      MvPolynomial.IsWeightedHomogeneous
        qsContactTransverseIntegerWeight S (t : ℤ) := by
    dsimp [S]
    exact HC4.Polynomial.initialForm_isWeightedHomogeneous
      qsContactTransverseIntegerWeight (t : ℤ) A
  have hSsource :
      ∀ q : Fin 3 →₀ ℕ,
        MvPolynomial.coeff q S ≠ 0 → MvPolynomial.coeff q A ≠ 0 := by
    intro q hq
    have hq' := hq
    dsimp [S] at hq'
    rw [HC4.Polynomial.coeff_initialForm] at hq'
    split at hq'
    · exact hq'
    · exact (hq' rfl).elim
  have hSexact :
      ∀ q : Fin 3 →₀ ℕ,
        MvPolynomial.coeff q S ≠ 0 → qsContactTransverseDegree q = t := by
    intro q hq
    have hq' := hq
    dsimp [S] at hq'
    rw [HC4.Polynomial.coeff_initialForm] at hq'
    split at hq'
    · have hw :
          Finsupp.weight qsContactTransverseIntegerWeight q = (t : ℤ) := ‹_›
      rw [weight_qsContactTransverseIntegerWeight] at hw
      exact_mod_cast hw
    · exact (hq' rfl).elim
  have hmax' :
      ∀ q : Fin 3 →₀ ℕ,
        MvPolynomial.coeff q A ≠ 0 → qsContactTransverseDegree q ≤ t := by
    intro q hq
    exact hmax q (MvPolynomial.mem_support_iff.mpr hq)
  exact ⟨{
    transverseDegree := t
    slice := S
    slice_eq := rfl
    slice_ne_zero := hSne
    slice_homogeneous := hShom
    slice_source := by simpa [A] using hSsource
    slice_exact_transverseDegree := hSexact
    transverseDegree_max := by simpa [A] using hmax'
  }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
