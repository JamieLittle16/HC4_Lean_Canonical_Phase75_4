import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactSchurClock
import Mathlib.Tactic

/-!
# A19.121: exact contact-Rees layer grading dictionary

The contact family is not globally homogeneous.  Its parameter exponent records
exactly the deficit from the contact source weight

    ordinaryDegree4 d + contactGap * d₀.

This is the bookkeeping needed before identifying any Schur coefficient with a
stationary weighted-profile coefficient.  In particular, no source monomial is
silently promoted to the contact special fibre: its precise Rees order remains
visible in the statement below.
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

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
