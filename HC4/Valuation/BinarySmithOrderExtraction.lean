import HC4.Valuation.SymmetricSmithImprovementRestart
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Binary Smith coefficient-order extraction

The fixed symmetric Smith separator from Phase 93.62 has denominator `10`
and universal correction bound `-4`.  Consequently the global Smith
dispatcher does not need the full `X`-adic order of every projected
coefficient class.

It only needs to know whether a class:

* survives on the special fibre (`order = 0`), or
* vanishes on the special fibre, hence every coefficient in that class is
  divisible by `X` (`order = 1`).

This file extracts exactly that binary order directly from the genuine Rees
family.

For a projected Smith exponent `e`, define `smithBinaryBase P e` to be zero
iff some source coefficient projecting to `e` has nonzero constant
coefficient.  Otherwise it is one.

We prove:

* every source coefficient is divisible by
      X^(smithBinaryBase P projection);
* the special-fibre projected support is exactly the set of family
  projections with binary base zero;
* strict symmetric improvement on the special-fibre support extends to
  strict improvement on the entire Rees-family support:
    - base-zero classes use the assumed strict improvement;
    - base-one classes contribute `10`, while the universal Smith
      correction is at least `-4`, so their denominator-cleared tilted
      value is automatically positive.

This is the missing support/order extraction needed to feed the strict
branch into the green Phase 93.63 restart theorem.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Binary coefficient order -/

/-- A projected Smith class is visible on the special fibre when at least
one source coefficient in that class has nonzero constant coefficient. -/
def SmithProjectionSurvivesSpecialFiber
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (e : SmithSupportExponent) : Prop :=
  ∃ d ∈ P.support,
    smithAxisProjection d = e ∧
      Polynomial.constantCoeff
        (MvPolynomial.coeff d P) ≠ 0

/-- Binary `X`-adic lower bound for one projected Smith class.

`0` means the class survives at `tau = 0`; `1` means all coefficients in
the class vanish at `tau = 0`. -/
noncomputable def smithBinaryBase
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (e : SmithSupportExponent) : ℕ := by
  classical
  exact
    if SmithProjectionSurvivesSpecialFiber P e
    then 0
    else 1

theorem smithBinaryBase_eq_zero_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (e : SmithSupportExponent) :
    smithBinaryBase P e = 0 ↔
      SmithProjectionSurvivesSpecialFiber P e := by
  classical
  unfold smithBinaryBase
  by_cases h :
      SmithProjectionSurvivesSpecialFiber P e
  · simp [h]
  · simp [h]

theorem smithBinaryBase_eq_one_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (e : SmithSupportExponent) :
    smithBinaryBase P e = 1 ↔
      ¬ SmithProjectionSurvivesSpecialFiber P e := by
  classical
  unfold smithBinaryBase
  by_cases h :
      SmithProjectionSurvivesSpecialFiber P e
  · simp [h]
  · simp [h]

theorem smithBinaryBase_zero_or_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (e : SmithSupportExponent) :
    smithBinaryBase P e = 0 ∨
      smithBinaryBase P e = 1 := by
  classical
  by_cases h :
      SmithProjectionSurvivesSpecialFiber P e
  · left
    exact
      (smithBinaryBase_eq_zero_iff P e).2 h
  · right
    exact
      (smithBinaryBase_eq_one_iff P e).2 h

/-! ## Automatic coefficient divisibility -/

/-- **The binary base is an honest coefficient-order lower bound.**

If the class survives, the required power is `X^0`.
If it does not survive, every coefficient in that class has zero constant
coefficient, hence is divisible by `X`. -/
theorem smithBinaryBase_coefficientOrderLowerBound
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    HasSmithCoefficientOrderLowerBound
      (smithBinaryBase P) P := by
  intro d hd
  rcases
      smithBinaryBase_zero_or_one
        P (smithAxisProjection d) with
    hzero | hone
  · rw [hzero]
    simp
  · rw [hone]
    simp only [pow_one]
    rw [Polynomial.X_dvd_iff]
    have hnosurvive :
        ¬ SmithProjectionSurvivesSpecialFiber
            P (smithAxisProjection d) :=
      (smithBinaryBase_eq_one_iff
        P (smithAxisProjection d)).1 hone
    by_contra hc
    apply hnosurvive
    exact
      ⟨d, hd, rfl, hc⟩

/-! ## Exact special-fibre support -/

/-- A source monomial survives in the polynomial-family special fibre iff
it was in the family support and its parameter coefficient has nonzero
constant term. -/
theorem mem_polynomialFamilySpecialFiber_support_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    d ∈ (polynomialFamilySpecialFiber P).support ↔
      d ∈ P.support ∧
        Polynomial.constantCoeff
          (MvPolynomial.coeff d P) ≠ 0 := by
  constructor
  · intro hdF
    have hspecialNe :
        MvPolynomial.coeff d
            (polynomialFamilySpecialFiber P) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hdF
    have hcne :
        Polynomial.constantCoeff
            (MvPolynomial.coeff d P) ≠ 0 := by
      intro hczero
      apply hspecialNe
      unfold polynomialFamilySpecialFiber
      rw [MvPolynomial.coeff_map]
      exact hczero
    have hdP :
        d ∈ P.support := by
      apply MvPolynomial.mem_support_iff.mpr
      intro hcoeffZero
      apply hcne
      rw [hcoeffZero]
      simp
    exact ⟨hdP, hcne⟩
  · rintro ⟨hdP, hcne⟩
    apply MvPolynomial.mem_support_iff.mpr
    unfold polynomialFamilySpecialFiber
    rw [MvPolynomial.coeff_map]
    exact hcne

/-- The field-valued Smith projection used by the local classifier agrees
with `smithAxisProjection` in the canonical `Fin 4` chart. -/
theorem smithSupportExponentOf_one_two_three_eq
    (d : Fin 4 →₀ ℕ) :
    smithSupportExponentOf
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4) d =
      smithAxisProjection d := by
  rfl

/-- **Special-fibre projected support = binary-base-zero family support.** -/
theorem smithProjectedSupport_specialFiber_iff
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (e : SmithSupportExponent) :
    e ∈
        smithProjectedSupport
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (polynomialFamilySpecialFiber P) ↔
      e ∈ smithAxisProjectedSupport (K := K) P ∧
        smithBinaryBase P e = 0 := by
  classical
  constructor
  · intro he
    unfold smithProjectedSupport at he
    rcases Finset.mem_image.mp he with
      ⟨d, hdF, hproj⟩
    have hdData :=
      (mem_polynomialFamilySpecialFiber_support_iff
        P d).1 hdF
    have hfamily :
        e ∈ smithAxisProjectedSupport (K := K) P := by
      unfold smithAxisProjectedSupport
      apply Finset.mem_image.mpr
      refine ⟨d, hdData.1, ?_⟩
      simpa [smithAxisProjection] using hproj
    have hsurvive :
        SmithProjectionSurvivesSpecialFiber P e := by
      refine ⟨d, hdData.1, ?_, hdData.2⟩
      simpa [smithAxisProjection] using hproj
    exact
      ⟨hfamily,
        (smithBinaryBase_eq_zero_iff P e).2
          hsurvive⟩
  · rintro ⟨heFamily, hbase0⟩
    have hsurvive :
        SmithProjectionSurvivesSpecialFiber P e :=
      (smithBinaryBase_eq_zero_iff P e).1 hbase0
    rcases hsurvive with
      ⟨d, hdP, hproj, hcne⟩
    have hdF :
        d ∈
          (polynomialFamilySpecialFiber P).support :=
      (mem_polynomialFamilySpecialFiber_support_iff
        P d).2 ⟨hdP, hcne⟩
    unfold smithProjectedSupport
    apply Finset.mem_image.mpr
    refine ⟨d, hdF, ?_⟩
    simpa [smithAxisProjection] using hproj

/-- A special-fibre projected exponent has binary base zero. -/
theorem smithBinaryBase_eq_zero_of_mem_specialFiberProjectedSupport
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {e : SmithSupportExponent}
    (he :
      e ∈
        smithProjectedSupport
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (polynomialFamilySpecialFiber P)) :
    smithBinaryBase P e = 0 :=
  ((smithProjectedSupport_specialFiber_iff P e).1 he).2

/-! ## Extending strict improvement off the special fibre -/

/-- A binary-base-one class is automatically strictly improved by the
fixed denominator-ten symmetric separator.

The universal separator correction is at least `-4`, while the base
contributes `10`. -/
theorem symmetricSmithTilt_positive_of_binaryBase_one
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (e : SmithSupportExponent)
    (hone : smithBinaryBase P e = 1) :
    smithRescaledOldMinimum 1 1 (0 : ℤ) <
      smithIntegralSeparatorTilt
        1 1
        (fun u => (smithBinaryBase P u : ℤ))
        e := by
  have hdelta :
      (-4 : ℤ) ≤ smithSeparatorDelta 1 1 e := by
    have h :=
      smithSeparatorDelta_lower_bound 1 1 e
    simpa [smithExtremeSeparatorBound] using h
  unfold smithRescaledOldMinimum
  unfold smithIntegralSeparatorTilt
  unfold finiteIntegralRescaledTilt
  simp [finiteTiltDenominator,
    smithExtremeSeparatorBound, hone]
  omega

/-- Strict improvement on the genuine special-fibre support extends to the
entire Rees-family support using the automatic binary order.

This is the key finite extraction theorem.

* binary base `0`: the class is represented on the special fibre, so use
  the assumed strict special-fibre improvement;
* binary base `1`: denominator `10` dominates the universal negative Smith
  correction `-4`.
-/
theorem strictSymmetricImprovement_specialFiber_extends_family
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hstrictF :
      HasStrictSymmetricSmithImprovement
        (smithProjectedSupport
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ))) :
    HasStrictSymmetricSmithImprovement
      (smithAxisProjectedSupport (K := K) P)
      0
      (fun e => (smithBinaryBase P e : ℤ)) := by
  intro e heFamily
  rcases smithBinaryBase_zero_or_one P e with
    hzero | hone
  · have heF :
      e ∈
        smithProjectedSupport
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (polynomialFamilySpecialFiber P) :=
      (smithProjectedSupport_specialFiber_iff
        P e).2 ⟨heFamily, hzero⟩
    have hF := hstrictF e heF
    unfold smithIntegralSeparatorTilt
    unfold finiteIntegralRescaledTilt
    unfold smithIntegralSeparatorTilt at hF
    unfold finiteIntegralRescaledTilt at hF
    simpa only [hzero, Nat.cast_zero, mul_zero, zero_add] using hF
  · exact
      symmetricSmithTilt_positive_of_binaryBase_one
        P e hone

/-! ## Canonical special-fibre Smith dichotomy -/

/-- **Canonical binary-order Smith dichotomy for a genuine Rees family.**

Either the actual special fibre is symmetric-Smith minimal with old
minimum zero, or the strict complementary branch automatically extends to
the whole family with the concrete coefficient-order lower bound required
by Phase 93.63.
-/
theorem specialFiber_symmetricMinimal_or_familyStrictImprovement
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)) ∨
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)) := by
  rcases
      symmetricSmithPoleMinimal_or_strictImprovement
        (smithProjectedSupport
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)) with
    hmin | hstrict
  · exact Or.inl hmin
  · exact
      Or.inr
        (strictSymmetricImprovement_specialFiber_extends_family
          P hstrict)

/-- The strict branch of the canonical special-fibre dichotomy plugs
directly into the green fixed-scale Phase 93.63 restart theorem. -/
theorem specialFiber_notSymmetricMinimal_exactCollision_and_strictRestart
    {s : GlobalRestartState}
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hnotMinimal :
      ¬ IsSymmetricSmithPoleMinimal
        (smithProjectedSupport
          (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
          (polynomialFamilySpecialFiber P))
        0
        (fun _ => (0 : ℤ)))
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (a b : Fin 4 → Polynomial K)
    (haaxis :
      HasSmithTransverseParameterFactor a)
    (hbaxis :
      HasSmithTransverseParameterFactor b)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (hs :
      s.defect = 10 * Delta)
    (newRepair : RepairState) :
    let base := smithBinaryBase P
    let Pram :=
      parameterRamificationFamily
        (K := K) 10 P
    let hstrict :
        HasStrictSymmetricSmithImprovement
          (smithAxisProjectedSupport (K := K) P)
          0
          (fun e => (base e : ℤ)) :=
      strictSymmetricImprovement_specialFiber_extends_family
        P
        (Or.resolve_left
          (symmetricSmithPoleMinimal_or_strictImprovement
            (smithProjectedSupport
              (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)
              (polynomialFamilySpecialFiber P))
            0
            (fun _ => (0 : ℤ)))
          hnotMinimal)
    let hsmith :=
      strictSymmetricImprovement_integralSmithDivisibility
        (K := K)
        base P
        (smithBinaryBase_coefficientOrderLowerBound P)
        hstrict
    let Psmith :=
      integralSmithConformalFamily
        2 2 Pram hsmith
    let hcommon :=
      strictSymmetricImprovement_commonParameterFactor
        (K := K)
        base P
        (smithBinaryBase_coefficientOrderLowerBound P)
        hstrict hsmith
    let Q :=
      commonParameterFactorFamily
        1 Psmith hcommon
    let t : GlobalRestartState :=
      { defect := 10 * Delta - 4
        repair := newRepair }
    HasPolynomialFamilyHessianDefect
        (K := K) Q (10 * Delta - 4) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  dsimp
  have hdich :=
    specialFiber_symmetricMinimal_or_familyStrictImprovement
      P
  have hstrict :
      HasStrictSymmetricSmithImprovement
        (smithAxisProjectedSupport (K := K) P)
        0
        (fun e => (smithBinaryBase P e : ℤ)) :=
    Or.resolve_left hdich hnotMinimal
  have hout :=
    strictSymmetricImprovement_exactCollision_and_strictRestart
      (K := K)
      (s := s)
      (smithBinaryBase P)
      P
      (smithBinaryBase_coefficientOrderLowerBound P)
      hstrict
      hdef
      a b haaxis hbaxis hcoll
      hs newRepair
  exact
    ⟨hout.1,
      hout.2.2.1,
      hout.2.2.2⟩

end

end HC4.Valuation
