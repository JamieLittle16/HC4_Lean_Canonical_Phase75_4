import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactSchurClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactLongitudinalProfile
import Mathlib.Tactic

/-!
# A19.121: exact contact-Rees layer grading dictionary

The contact family is not globally homogeneous.  Its parameter exponent records
exactly the deficit from the contact source weight

    ordinaryDegree4 d + contactGap * d₀.

Writing a source exponent as `m.cons n`, with `n` longitudinal and `m`
transverse, this is exactly

    transverseDegree(m) + (contactGap + 1) * n.

This is the bookkeeping needed before identifying any Schur coefficient with a
stationary weighted-profile coefficient.  In particular, no source monomial is
silently promoted to the contact special fibre: its precise Rees order remains
visible in the statements below.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Ordinary total degree of a transverse three-variable exponent. -/
def qsContactTransverseDegree (m : Fin 3 →₀ ℕ) : ℕ :=
  m 0 + m 1 + m 2

/-- The integral contact weight splits exactly into transverse degree plus the
binary longitudinal weight `r+1`. -/
theorem qsIntegralContactWeight_cons
    (r n : ℕ) (m : Fin 3 →₀ ℕ) :
    Finsupp.weight (qsIntegralContactWeight r) (m.cons n) =
      qsContactTransverseDegree m + (r + 1) * n := by
  rw [qsIntegralContactWeight_finsupp]
  have h1 : (m.cons n) (1 : Fin 4) = m (0 : Fin 3) := by
    change Finsupp.cons n m (Fin.succ (0 : Fin 3)) = m (0 : Fin 3)
    exact Finsupp.cons_succ (0 : Fin 3) n m
  have h2 : (m.cons n) (2 : Fin 4) = m (1 : Fin 3) := by
    change Finsupp.cons n m (Fin.succ (1 : Fin 3)) = m (1 : Fin 3)
    exact Finsupp.cons_succ (1 : Fin 3) n m
  have h3 : (m.cons n) (3 : Fin 4) = m (2 : Fin 3) := by
    change Finsupp.cons n m (Fin.succ (2 : Fin 3)) = m (2 : Fin 3)
    exact Finsupp.cons_succ (2 : Fin 3) n m
  simp [HC4.Polynomial.ordinaryDegree4, qsContactTransverseDegree, h1, h2, h3]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Exact source-coefficient formula for every layer of the canonical integral
contact Rees. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_parameterLayer_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (n : ℕ) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (familyParameterLayer P.contactFamily n) =
      if d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support ∧
          T.topFace.degree -
            (HC4.Polynomial.ordinaryDegree4 d +
              P.contactGap * d (0 : Fin 4)) = n then
        MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      else 0 := by
  rw [QsOtherFacetContactQuadraticReesPackage.contactFamily]
  rw [reverseWeightedReesFamily_parameterLayer_coeff]
  rw [qsIntegralContactWeight_finsupp]

/-- A supported source monomial occurs in exactly the parameter layer given by
its contact-weight deficit. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_source_coeff_at_deficit
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support) :
    MvPolynomial.coeff d
        (familyParameterLayer P.contactFamily
          (T.topFace.degree -
            (HC4.Polynomial.ordinaryDegree4 d +
              P.contactGap * d (0 : Fin 4)))) =
      MvPolynomial.coeff d
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  rw [P.contactFamily_parameterLayer_coeff]
  simp [hd]

/-- Coefficientwise longitudinal/transverse form of the contact grading.  The
source coefficient on the right is exactly the corresponding coefficient of
the A19.114 symbolic longitudinal profile. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_longitudinal_transverse_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (q n : ℕ) (m : Fin 3 →₀ ℕ) :
    MvPolynomial.coeff (m.cons n) (familyParameterLayer P.contactFamily q) =
      if m.cons n ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support ∧
          T.topFace.degree -
            (qsContactTransverseDegree m + P.profileWeight * n) = q then
        MvPolynomial.coeff m
          ((qsContactRawLongitudinalProfile (K := K) (T := T)).coeff n)
      else 0 := by
  rw [P.contactFamily_parameterLayer_coeff]
  have hweight :
      HC4.Polynomial.ordinaryDegree4 (m.cons n) +
          P.contactGap * (m.cons n) (0 : Fin 4) =
        qsContactTransverseDegree m + P.profileWeight * n := by
    rw [P.profileWeight_eq]
    have h := qsIntegralContactWeight_cons P.contactGap n m
    rw [qsIntegralContactWeight_finsupp] at h
    exact h
  rw [hweight]
  unfold qsContactRawLongitudinalProfile
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]

/-- Every transverse monomial occurring in longitudinal profile slice `n`
uses at most the contact weight left after paying the binary longitudinal
cost `profileWeight * n`.  This is the exact support budget needed by the
R18.21 extremal correction calculation. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.transverseDegree_add_profileWeight_mul_le
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {n : ℕ} {m : Fin 3 →₀ ℕ}
    (hm : m ∈ (R.profile.coeff n).support) :
    qsContactTransverseDegree m + P.profileWeight * n ≤ T.topFace.degree := by
  have hcoeff : MvPolynomial.coeff m (R.profile.coeff n) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [R.profile_eq, qsContactRawLongitudinalProfile,
    MvPolynomial.finSuccEquiv_coeff_coeff] at hcoeff
  have hsource :
      m.cons n ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hbound := P.bound (m.cons n) hsource
  rw [qsIntegralContactWeight_cons, ← P.profileWeight_eq] at hbound
  exact hbound

/-- Equivalently, the transverse total degree of slice `n` is bounded by its
pure binary parameter order `D - profileWeight*n`. -/
theorem QsOtherFacetContactRawLongitudinalProfilePackage.transverseDegree_le_profileOrder
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetContactQuadraticReesPackage C}
    (R : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    {n : ℕ} {m : Fin 3 →₀ ℕ}
    (hm : m ∈ (R.profile.coeff n).support) :
    qsContactTransverseDegree m ≤ T.topFace.degree - P.profileWeight * n := by
  have h := R.transverseDegree_add_profileWeight_mul_le hm
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
