import HC4.Valuation.StrictSmithFirstContactMinimum
import HC4.Valuation.CanonicalSmithDefectExposure
import Mathlib.Tactic

/-!
# Canonical strict-Smith visible first-contact rigidity

In the sub-six first-contact regime, the previous file proves that every
survivor of the maximally-normalised strict-Smith face came from exact
source order zero.  Hence the new first-contact support is contained in the
old special-fibre support.

This file records the next finite dichotomy.

Either the visible first-contact face drops at least one old special-fibre
monomial, so it is a genuine proper subface; or every old special-fibre
monomial survives.  In the latter case every such monomial has the same
positive Smith residual `raw(d) - 4`, namely the attained first-contact
order.

No global progress relation is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Below the hidden-layer threshold `6`, the maximally-normalised strict
Smith first-contact support is contained in the original special-fibre
support. -/
theorem canonicalStrictSmith_firstContact_support_subset_specialFiber_of_order_lt_six
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hfirst :
      canonicalStrictSmithFirstContactOrder P hstrict hP < 6) :
    (polynomialFamilySpecialFiber
        (canonicalMaximallyNormalizedStrictSmithFamily
          P hstrict hP)).support ⊆
      (polynomialFamilySpecialFiber P).support := by
  intro d hd
  have hzero :=
    canonicalStrictSmith_firstContact_survivor_visible_of_order_lt_six
      (K := K) P hstrict hP hfirst hd
  have hdData :=
    (mem_canonicalStrictSmithFirstContact_iff
      (K := K) P hstrict hP d).1 hd
  have hdSource :
      d ∈ P.support :=
    mem_strictSymmetricSmithTransformedFamily_support_imp_source_support
      (K := K)
      (smithBinaryBase P) P
      (smithBinaryBase_coefficientOrderLowerBound P)
      hstrict hdData.1
  exact
    (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
      P hdSource).1 hzero

/-- In the sub-six regime there are exactly two visible possibilities.

Either some old special-fibre monomial is lost at first contact, giving a
proper visible subface; or every old special-fibre monomial survives, in
which case all of them have one common positive Smith residual
`raw(d) - 4`, equal to the attained first-contact order. -/
theorem canonicalStrictSmith_firstContact_proper_or_constantResidual_of_order_lt_six
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hfirst :
      canonicalStrictSmithFirstContactOrder P hstrict hP < 6) :
    (∃ d ∈ (polynomialFamilySpecialFiber P).support,
        d ∉
          (polynomialFamilySpecialFiber
            (canonicalMaximallyNormalizedStrictSmithFamily
              P hstrict hP)).support) ∨
      (∀ d ∈ (polynomialFamilySpecialFiber P).support,
        smithConformalRawExponent 2 2 d - 4 =
          canonicalStrictSmithFirstContactOrder P hstrict hP) := by
  classical
  by_cases hproper :
      ∃ d ∈ (polynomialFamilySpecialFiber P).support,
        d ∉
          (polynomialFamilySpecialFiber
            (canonicalMaximallyNormalizedStrictSmithFamily
              P hstrict hP)).support
  · exact Or.inl hproper
  · right
    intro d hdOld
    have hdNew :
        d ∈
          (polynomialFamilySpecialFiber
            (canonicalMaximallyNormalizedStrictSmithFamily
              P hstrict hP)).support := by
      by_contra hnot
      exact hproper ⟨d, hdOld, hnot⟩
    have hdData :=
      (mem_canonicalStrictSmithFirstContact_iff
        (K := K) P hstrict hP d).1 hdNew
    have hdSource :
        d ∈ P.support :=
      (mem_polynomialFamilySpecialFiber_support_iff P d).1 hdOld |>.1
    have hzero :
        smithFamilyCoefficientOrder P d = 0 :=
      (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
        P hdSource).2 hdOld
    have htrans :
        smithFamilyCoefficientOrder
            (canonicalStrictSmithTransformedFamily P hstrict) d =
          smithConformalRawExponent 2 2 d - 4 := by
      simpa [canonicalStrictSmithTransformedFamily] using
        (canonicalStrictSmith_transformedOrder_eq_raw_sub_four_of_sourceOrder_zero
          (K := K) P hstrict hdSource hzero)
    exact htrans.symm.trans hdData.2

end

end HC4.Valuation
