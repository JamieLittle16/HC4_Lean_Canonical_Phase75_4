import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingRelativeFirstLayer
import Mathlib.Tactic

/-!
# Layer shift under the relative first-deformation quotient

If `j` is the least positive actual parameter order of a family `P`, the
relative first-deformation construction writes

    P = P(0) + X^j Q.

The special-fibre theorem identifies `Q_0 = P_j`.  This file records the full
coefficientwise strengthening: every parameter layer is shifted exactly,

    Q_n = P_(j+n).

No geometry is involved; this is the algebraic recursion used by the later
staircase extraction.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-- **Exact layer shift after removing the first actual positive parameter
power.** -/
theorem firstActualDeformationFamily_parameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (n : ℕ) :
    familyParameterLayer (firstActualDeformationFamily P h) n =
      familyParameterLayer P
        (firstPositiveActualParameterOrder P h + n) := by
  let j := firstPositiveActualParameterOrder P h
  let R := positiveParameterRemainder P
  let hdiv : HasCommonParameterFactor j R :=
    positiveParameterRemainder_hasCommonParameterFactor_firstActual P h
  let Q := commonParameterFactorFamily j R hdiv
  have hjpos : 0 < j := by
    simpa [j] using firstPositiveActualParameterOrder_pos P h
  apply MvPolynomial.ext
  intro d
  rw [familyParameterLayer_coeff, familyParameterLayer_coeff]
  change (MvPolynomial.coeff d Q).coeff n =
    (MvPolynomial.coeff d P).coeff (j + n)
  have hfactor := commonParameterFactorFamily_coeff_factorisation
    j R hdiv d
  have hcoeff := congrArg (fun c : Polynomial K => c.coeff (j + n)) hfactor
  change
    (MvPolynomial.coeff d R).coeff (j + n) =
      (Polynomial.X ^ j * MvPolynomial.coeff d Q).coeff (j + n)
    at hcoeff
  have hleft :
      (MvPolynomial.coeff d R).coeff (j + n) =
        (MvPolynomial.coeff d P).coeff (j + n) := by
    have hsumpos : 0 < j + n := by omega
    simpa [R] using coeff_pos_positiveParameterRemainder P d hsumpos
  have hright :
      (Polynomial.X ^ j * MvPolynomial.coeff d Q).coeff (j + n) =
        (MvPolynomial.coeff d Q).coeff n := by
    rw [Polynomial.coeff_X_pow_mul']
    simp
  rw [hleft, hright] at hcoeff
  exact hcoeff.symm

/-- The same shift identity in the order preferred for rewriting later source
layers. -/
theorem familyParameterLayer_eq_firstActualDeformationFamily_parameterLayer
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P)
    (n : ℕ) :
    familyParameterLayer P
        (firstPositiveActualParameterOrder P h + n) =
      familyParameterLayer (firstActualDeformationFamily P h) n := by
  exact (firstActualDeformationFamily_parameterLayer P h n).symm

end

end HC4.Valuation
