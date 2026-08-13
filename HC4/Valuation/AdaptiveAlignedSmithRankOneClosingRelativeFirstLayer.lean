import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingActualLayer
import HC4.Valuation.AdaptiveRigidMatrixExposure
import Mathlib.Tactic

/-!
# Relative first actual deformation at a rank-one closing

A positive closing layer should not be exposed against the whole family
while the old special fibre is still present.  The honest object is the
positive-parameter remainder

    P⁺(τ) = P(τ) - P(0).

If `j > 0` is the least *actual* positive parameter exponent occurring in
`P`, then every coefficient of `P⁺` is divisible by `τ^j`.  We may therefore
write canonically

    P(τ) = P(0) + τ^j Q(τ).

The special fibre of the quotient is exactly the genuine coefficient
potential

    Q(0) = P_j.

This is a relative first-contact construction: it freezes the complete old
special fibre before exposing the first deformation.  It uses no supporting
hyperplane and no JC2 input.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K]

/-! ## Coefficients of the positive-parameter remainder -/

/-- Exact coefficient of the positive-parameter remainder. -/
theorem coeff_positiveParameterRemainder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (positiveParameterRemainder P) =
      MvPolynomial.coeff d P -
        Polynomial.C
          (Polynomial.constantCoeff (MvPolynomial.coeff d P)) := by
  unfold positiveParameterRemainder
  rw [MvPolynomial.coeff_sub, coeff_constantPolynomialFamily,
    coeff_polynomialFamilySpecialFiber]

/-- Every remainder coefficient has zero constant term. -/
theorem coeff_zero_positiveParameterRemainder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    (MvPolynomial.coeff d (positiveParameterRemainder P)).coeff 0 = 0 := by
  rw [coeff_positiveParameterRemainder]
  simp [Polynomial.constantCoeff]

/-- At every strictly positive parameter exponent, subtracting the special
fibre changes nothing. -/
theorem coeff_pos_positiveParameterRemainder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    {n : ℕ}
    (hn : 0 < n) :
    (MvPolynomial.coeff d (positiveParameterRemainder P)).coeff n =
      (MvPolynomial.coeff d P).coeff n := by
  rw [coeff_positiveParameterRemainder]
  rw [Polynomial.coeff_sub, Polynomial.coeff_C]
  simp [Nat.ne_of_gt hn]

/-! ## Divisibility by the first actual positive layer -/

/-- The positive-parameter remainder is divisible coefficientwise by the
least actual positive parameter exponent of the family. -/
theorem positiveParameterRemainder_hasCommonParameterFactor_firstActual
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    HasCommonParameterFactor
      (firstPositiveActualParameterOrder P h)
      (positiveParameterRemainder P) := by
  intro d hd
  rw [Polynomial.X_pow_dvd_iff]
  intro n hnlt
  by_cases hn0 : n = 0
  · subst n
    exact coeff_zero_positiveParameterRemainder P d
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [coeff_pos_positiveParameterRemainder P d hnpos]
    by_contra hcoeff
    have hdP : d ∈ P.support := by
      apply MvPolynomial.mem_support_iff.mpr
      intro hzero
      rw [hzero] at hcoeff
      simp at hcoeff
    have hnmem :
        n ∈ familyParameterLayerOrders P := by
      exact
        (mem_familyParameterLayerOrders_iff P n).2
          ⟨d, hdP, hcoeff⟩
    have hle :
        firstPositiveActualParameterOrder P h ≤ n :=
      firstPositiveActualParameterOrder_le
        P h hnmem hnpos
    omega

/-- Canonical quotient after freezing the special fibre and removing the
least actual positive parameter power. -/
noncomputable def firstActualDeformationFamily
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  commonParameterFactorFamily
    (firstPositiveActualParameterOrder P h)
    (positiveParameterRemainder P)
    (positiveParameterRemainder_hasCommonParameterFactor_firstActual P h)

/-- Exact relative first-deformation factorisation

    P = P(0) + τ^j Q.
-/
theorem firstActualDeformationFamily_factorisation
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    P =
      constantPolynomialFamily (polynomialFamilySpecialFiber P) +
        MvPolynomial.C
            (Polynomial.X ^ firstPositiveActualParameterOrder P h) *
          firstActualDeformationFamily P h := by
  let j := firstPositiveActualParameterOrder P h
  let R := positiveParameterRemainder P
  let hdiv :
      HasCommonParameterFactor j R :=
    positiveParameterRemainder_hasCommonParameterFactor_firstActual P h
  have hfactor :
      R =
        MvPolynomial.C (Polynomial.X ^ j) *
          commonParameterFactorFamily j R hdiv :=
    commonParameterFactorFamily_factorisation j R hdiv
  calc
    P =
        constantPolynomialFamily (polynomialFamilySpecialFiber P) +
          positiveParameterRemainder P := by
      unfold positiveParameterRemainder
      abel
    _ =
        constantPolynomialFamily (polynomialFamilySpecialFiber P) +
          MvPolynomial.C (Polynomial.X ^ j) *
            commonParameterFactorFamily j R hdiv := by
      simpa [R] using congrArg
        (fun Q =>
          constantPolynomialFamily (polynomialFamilySpecialFiber P) + Q)
        hfactor
    _ = _ := by
      simp [firstActualDeformationFamily, j, R, hdiv]

/-- **Relative first-contact identity.**

The special fibre of the quotient is exactly the genuine first positive
coefficient potential `P_j`. -/
theorem firstActualDeformationFamily_specialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    polynomialFamilySpecialFiber (firstActualDeformationFamily P h) =
      familyParameterLayer P
        (firstPositiveActualParameterOrder P h) := by
  let j := firstPositiveActualParameterOrder P h
  let R := positiveParameterRemainder P
  let hdiv :
      HasCommonParameterFactor j R :=
    positiveParameterRemainder_hasCommonParameterFactor_firstActual P h
  let Q := commonParameterFactorFamily j R hdiv
  have hjpos : 0 < j := by
    simpa [j] using firstPositiveActualParameterOrder_pos P h
  apply MvPolynomial.ext
  intro d
  rw [coeff_polynomialFamilySpecialFiber, familyParameterLayer_coeff]
  change
    Polynomial.constantCoeff (MvPolynomial.coeff d Q) =
      (MvPolynomial.coeff d P).coeff j
  change
    (MvPolynomial.coeff d Q).coeff 0 =
      (MvPolynomial.coeff d P).coeff j
  have hfactor :=
    commonParameterFactorFamily_coeff_factorisation
      j R hdiv d
  have hcoeff :=
    congrArg (fun c : Polynomial K => c.coeff j) hfactor
  change
    (MvPolynomial.coeff d R).coeff j =
      (Polynomial.X ^ j * MvPolynomial.coeff d Q).coeff j
    at hcoeff
  have hleft :
      (MvPolynomial.coeff d R).coeff j =
        (MvPolynomial.coeff d P).coeff j := by
    simpa [R] using
      coeff_pos_positiveParameterRemainder P d hjpos
  have hright :
      (Polynomial.X ^ j * MvPolynomial.coeff d Q).coeff j =
        (MvPolynomial.coeff d Q).coeff 0 := by
    rw [Polynomial.coeff_X_pow_mul']
    simp
  rw [hleft, hright] at hcoeff
  exact hcoeff.symm

/-- The relative first deformation is nonzero, because its special fibre is
the selected nonzero actual parameter layer. -/
theorem firstActualDeformationFamily_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasPositiveActualParameterLayer P) :
    firstActualDeformationFamily P h ≠ 0 := by
  intro hzero
  have hspecial :=
    firstActualDeformationFamily_specialFiber P h
  rw [hzero] at hspecial
  have hzeroSpecial :
      polynomialFamilySpecialFiber
          (0 : MvPolynomial (Fin 4) (Polynomial K)) =
        (0 : MvPolynomial (Fin 4) K) := by
    unfold polynomialFamilySpecialFiber
    simp
  rw [hzeroSpecial] at hspecial
  exact
    (firstPositiveActualParameterLayer_ne_zero P h)
      hspecial.symm

/-! ## Rank-one closing specialisation -/

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable [CharZero K]
variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Canonical relative first deformation of the honest right-recentered
rank-one closing source. -/
noncomputable def relativeFirstActualDeformationFamily
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  firstActualDeformationFamily C.family C.hasPositiveActualParameterLayer

/-- Exact decomposition of the honest closing source into its frozen special
fibre and its first positive deformation tail. -/
theorem relativeFirstActualDeformation_factorisation
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.family =
      constantPolynomialFamily (polynomialFamilySpecialFiber C.family) +
        MvPolynomial.C (Polynomial.X ^ C.firstActualLayerOrder) *
          C.relativeFirstActualDeformationFamily := by
  simpa [relativeFirstActualDeformationFamily,
    firstActualLayerOrder] using
    firstActualDeformationFamily_factorisation
      C.family C.hasPositiveActualParameterLayer

/-- The special fibre of the relative deformation is the *actual* first
positive coefficient potential of the same honest chart-aware source. -/
theorem relativeFirstActualDeformation_specialFiber
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    polynomialFamilySpecialFiber
        C.relativeFirstActualDeformationFamily =
      familyParameterLayer C.family C.firstActualLayerOrder := by
  simpa [relativeFirstActualDeformationFamily,
    firstActualLayerOrder] using
    firstActualDeformationFamily_specialFiber
      C.family C.hasPositiveActualParameterLayer

/-- In particular the relative first deformation is genuinely nonzero. -/
theorem relativeFirstActualDeformation_ne_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    C.relativeFirstActualDeformationFamily ≠ 0 := by
  simpa [relativeFirstActualDeformationFamily] using
    firstActualDeformationFamily_ne_zero
      C.family C.hasPositiveActualParameterLayer

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
