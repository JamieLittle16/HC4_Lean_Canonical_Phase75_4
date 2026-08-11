import HC4.Valuation.StrictSmithVisibleHiddenGap
import HC4.Valuation.StrictSmithMaximalNormalization
import Mathlib.Tactic

/-!
# Canonical strict-Smith first-contact minimum

This file connects the visible/hidden transformed-order gap to the actual
maximally-normalised strict-Smith first-contact face.

The key consequence is simple but important: if the attained transformed
common parameter order is strictly less than `6`, then every exponent
surviving the maximally-normalised first-contact special fibre must come from
an original exact-order-zero source coefficient.  Hence no genuinely hidden
higher parameter layer can participate in that first contact.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Ramification cannot create a new source monomial. -/
theorem mem_parameterRamificationFamily_support_imp_source_support
    (R : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {d : Fin 4 →₀ ℕ}
    (hd :
      d ∈ (parameterRamificationFamily (K := K) R P).support) :
    d ∈ P.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hzero
  have hcoeffzero :
      MvPolynomial.coeff d
          (parameterRamificationFamily (K := K) R P) = 0 := by
    unfold parameterRamificationFamily
    rw [MvPolynomial.coeff_map, hzero]
    simp
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeffzero

/-- The strict-Smith transform introduces no new source monomials relative
to the original family. -/
theorem mem_strictSymmetricSmithTransformedFamily_support_imp_source_support
    (base : SmithSupportExponent → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hbase : HasSmithCoefficientOrderLowerBound base P)
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (base e : ℤ)))
    {d : Fin 4 →₀ ℕ}
    (hd :
      d ∈
        (strictSymmetricSmithTransformedFamily
          base P hbase hstrict).support) :
    d ∈ P.support := by
  let Pram := parameterRamificationFamily (K := K) 10 P
  let hsmith :=
    strictSymmetricImprovement_integralSmithDivisibility
      (K := K) base P hbase hstrict
  have hdRam : d ∈ Pram.support := by
    dsimp [strictSymmetricSmithTransformedFamily] at hd
    exact
      support_integralSmithConformalFamily_subset
        2 2 Pram hsmith hd
  exact
    mem_parameterRamificationFamily_support_imp_source_support
      (K := K) 10 P hdRam

/-- Canonical binary strict Smith transform. -/
noncomputable def canonicalStrictSmithTransformedFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ))) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  strictSymmetricSmithTransformedFamily
    (smithBinaryBase P) P
    (smithBinaryBase_coefficientOrderLowerBound P)
    hstrict

/-- The canonical strict Smith family is nonzero whenever the source family
is nonzero. -/
theorem canonicalStrictSmithTransformedFamily_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0) :
    canonicalStrictSmithTransformedFamily P hstrict ≠ 0 := by
  unfold canonicalStrictSmithTransformedFamily
  exact
    strictSymmetricImprovement_transformedFamily_ne_zero
      (K := K)
      (smithBinaryBase P) P
      (smithBinaryBase_coefficientOrderLowerBound P)
      hstrict hP

/-- Strict symmetric improvement leaves at least one common parameter factor
in the canonical transformed family. -/
theorem canonicalStrictSmithTransformedFamily_commonFactor_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ))) :
    HasCommonParameterFactor
      1
      (canonicalStrictSmithTransformedFamily P hstrict) := by
  let hbase := smithBinaryBase_coefficientOrderLowerBound P
  let hsmith :=
    strictSymmetricImprovement_integralSmithDivisibility
      (K := K) (smithBinaryBase P) P hbase hstrict
  unfold canonicalStrictSmithTransformedFamily
  exact
    strictSymmetricImprovement_commonParameterFactor
      (K := K)
      (smithBinaryBase P) P hbase hstrict hsmith

/-- The actual maximal common parameter order of the canonical strict Smith
transform. -/
noncomputable def canonicalStrictSmithFirstContactOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0) : ℕ :=
  strictSmithCommonParameterOrder
    (canonicalStrictSmithTransformedFamily P hstrict)
    (canonicalStrictSmithTransformedFamily_ne_zero P hstrict hP)
    (canonicalStrictSmithTransformedFamily_commonFactor_one P hstrict)

/-- The maximally-normalised canonical strict Smith family. -/
noncomputable def canonicalMaximallyNormalizedStrictSmithFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  maximallyNormalizedStrictSmithFamily
    (canonicalStrictSmithTransformedFamily P hstrict)
    (canonicalStrictSmithTransformedFamily_ne_zero P hstrict hP)
    (canonicalStrictSmithTransformedFamily_commonFactor_one P hstrict)

/-- Membership in the canonical maximally-normalised first-contact special
fibre gives both transformed support membership and attainment of the actual
minimum transformed coefficient order. -/
theorem mem_canonicalStrictSmithFirstContact_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (d : Fin 4 →₀ ℕ) :
    d ∈
        (polynomialFamilySpecialFiber
          (canonicalMaximallyNormalizedStrictSmithFamily
            P hstrict hP)).support ↔
      d ∈ (canonicalStrictSmithTransformedFamily P hstrict).support ∧
        smithFamilyCoefficientOrder
            (canonicalStrictSmithTransformedFamily P hstrict) d =
          canonicalStrictSmithFirstContactOrder P hstrict hP := by
  unfold canonicalMaximallyNormalizedStrictSmithFamily
  unfold canonicalStrictSmithFirstContactOrder
  exact
    mem_specialFiber_maximallyNormalizedStrictSmith_iff
      (K := K)
      (canonicalStrictSmithTransformedFamily P hstrict)
      (canonicalStrictSmithTransformedFamily_ne_zero P hstrict hP)
      (canonicalStrictSmithTransformedFamily_commonFactor_one P hstrict)
      d

/-- If the attained canonical strict-Smith first-contact order is below six,
then every surviving exponent came from the old exact-order-zero layer.
Thus no hidden positive-order source coefficient participates in such a
first contact. -/
theorem canonicalStrictSmith_firstContact_survivor_visible_of_order_lt_six
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hfirst :
      canonicalStrictSmithFirstContactOrder P hstrict hP < 6)
    {d : Fin 4 →₀ ℕ}
    (hd :
      d ∈
        (polynomialFamilySpecialFiber
          (canonicalMaximallyNormalizedStrictSmithFamily
            P hstrict hP)).support) :
    smithFamilyCoefficientOrder P d = 0 := by
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
  rcases
      canonicalStrictSmith_transformedOrder_visible_or_hidden
        (K := K) P hstrict hdSource with
    hvis | hhidden
  · exact hvis.1
  · have hge6 :
        6 ≤ canonicalStrictSmithFirstContactOrder P hstrict hP := by
      rw [← hdData.2]
      simpa [canonicalStrictSmithTransformedFamily] using hhidden.2
    omega

/-- In the sub-six regime, every surviving first-contact exponent also has
strictly positive canonical Smith separator. -/
theorem canonicalStrictSmith_firstContact_survivor_separator_pos_of_order_lt_six
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)))
    (hP : P ≠ 0)
    (hfirst :
      canonicalStrictSmithFirstContactOrder P hstrict hP < 6)
    {d : Fin 4 →₀ ℕ}
    (hd :
      d ∈
        (polynomialFamilySpecialFiber
          (canonicalMaximallyNormalizedStrictSmithFamily
            P hstrict hP)).support) :
    0 < smithSeparatorDelta 1 1 (smithAxisProjection d) := by
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
    canonicalStrictSmith_separatorDelta_pos_of_sourceOrder_zero
      (K := K) P hstrict hdSource hzero

end

end HC4.Valuation
