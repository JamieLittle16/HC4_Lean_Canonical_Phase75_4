import HC4.Valuation.AdaptiveAlignedSmithClosingFirstContactLattice
import HC4.Newton.SmithFirstWallGradeClassification
import Mathlib.Tactic

/-!
# A19.17: determinant-closing transverse Rees frontier at positive clock

Let `Delta > 0` be the current Hessian determinant clock.  There is a canonical
transverse Rees scaling

    tau -> s^2,
    (x1,x2,x3) -> s^Delta (x1,x2,x3),
    F -> s^(-2*Delta) F.

If it is coefficientwise integral, the Hessian covariance formula is exact:

    2*Delta + 2*(3*Delta) - 4*(2*Delta) = 0.

Thus the transformed family has raw Hessian defect zero in one step.

The only possible obstruction to coefficientwise integrality is equally
concrete.  A failing supported monomial must have total transverse degree at
most one, hence its Smith exponent is exactly one of

    (0,0,0), (0,1,0), (1,0,0), (0,0,1).

These are precisely the four historical low blocker patterns.  This file
therefore turns the positive-clock quadratic problem into an honest dichotomy:
low blocker layer, or an actual determinant-one Rees family.  It does not yet
assert transport of the marked moving section; that is the next source-facing
adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Uniform transverse source weight used by the determinant-closing Rees
scaling.  The distinguished longitudinal coordinate has weight zero. -/
def canonicalPositiveTransverseReesWeight
    (Delta : ℕ) (i : Fin 4) : ℕ :=
  if i = 0 then 0 else Delta

@[simp] theorem canonicalPositiveTransverseReesWeight_zero
    (Delta : ℕ) :
    canonicalPositiveTransverseReesWeight Delta (0 : Fin 4) = 0 := by
  simp [canonicalPositiveTransverseReesWeight]

@[simp] theorem canonicalPositiveTransverseReesWeight_one
    (Delta : ℕ) :
    canonicalPositiveTransverseReesWeight Delta (1 : Fin 4) = Delta := by
  simp [canonicalPositiveTransverseReesWeight]

@[simp] theorem canonicalPositiveTransverseReesWeight_two
    (Delta : ℕ) :
    canonicalPositiveTransverseReesWeight Delta (2 : Fin 4) = Delta := by
  simp [canonicalPositiveTransverseReesWeight]

@[simp] theorem canonicalPositiveTransverseReesWeight_three
    (Delta : ℕ) :
    canonicalPositiveTransverseReesWeight Delta (3 : Fin 4) = Delta := by
  simp [canonicalPositiveTransverseReesWeight]

/-- Total transverse source degree. -/
def canonicalTransverseDegree (d : Fin 4 →₀ ℕ) : ℕ :=
  d 1 + d 2 + d 3

/-- The Rees weighted degree is `Delta` times total transverse degree. -/
theorem canonicalPositiveTransverseReesWeight_finsupp
    (Delta : ℕ) (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d =
      Delta * canonicalTransverseDegree d := by
  rw [Finsupp.weight_apply]
  simp [Finsupp.sum_fintype, Fin.sum_univ_four,
    canonicalPositiveTransverseReesWeight, canonicalTransverseDegree]
  ring

/-- The sum of the four source weights is exactly `3*Delta`. -/
theorem canonicalPositiveTransverseReesWeight_sum
    (Delta : ℕ) :
    ∑ i : Fin 4, canonicalPositiveTransverseReesWeight Delta i =
      3 * Delta := by
  rw [Fin.sum_univ_four]
  simp [canonicalPositiveTransverseReesWeight]
  omega

/-- Exact coefficient-order inequality required by the determinant-closing
transverse Rees transform. -/
def HasCanonicalPositiveTransverseReesCoefficientBound
    (Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    2 * Delta ≤
      2 * smithFamilyCoefficientOrder P d +
        Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d

/-- A coefficient-order bound gives the literal coefficientwise divisibility
needed by `adaptiveSmithExposureFamily` at ramification `2` and level
`2*Delta`. -/
theorem HasCanonicalPositiveTransverseReesCoefficientBound.integralExposure
    {Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (h : HasCanonicalPositiveTransverseReesCoefficientBound Delta P) :
    HasIntegralAdaptiveSmithExposure
      2 (canonicalPositiveTransverseReesWeight Delta) (2 * Delta) P := by
  intro d hd
  let q := smithFamilyCoefficientOrder P d
  have hqdiv : Polynomial.X ^ q ∣ MvPolynomial.coeff d P :=
    smithFamilyCoefficientOrder_dvd P hd
  have hramdiv :
      Polynomial.X ^ (2 * q) ∣
        parameterRamificationHom (K := K) 2
          (MvPolynomial.coeff d P) :=
    parameterRamification_pow_dvd 2 q _ hqdiv
  have hle :
      2 * Delta ≤
        2 * q +
          Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d := by
    simpa [q] using h d hd
  rcases hramdiv with ⟨a, ha⟩
  refine ⟨Polynomial.X ^
      (2 * q +
        Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d -
        2 * Delta) * a, ?_⟩
  unfold adaptiveSmithExposureCoefficientFactor
  rw [ha]
  calc
    Polynomial.X ^
          Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d *
        (Polynomial.X ^ (2 * q) * a) =
      Polynomial.X ^
          (Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d +
            2 * q) * a := by
        rw [← mul_assoc, ← pow_add]
    _ = Polynomial.X ^ (2 * Delta) *
        (Polynomial.X ^
          (2 * q +
            Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d -
            2 * Delta) * a) := by
      rw [← mul_assoc, ← pow_add]
      congr 1
      omega

/-- The actual determinant-closing exposed family. -/
noncomputable def canonicalPositiveTransverseReesFamily
    (Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (h : HasCanonicalPositiveTransverseReesCoefficientBound Delta P) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  adaptiveSmithExposureFamily
    2 (canonicalPositiveTransverseReesWeight Delta) (2 * Delta)
    P h.integralExposure

/-- **Exact determinant closure.**

Whenever the transverse Rees transform is integral, a family of incoming raw
Hessian defect `Delta` is sent to raw defect zero exactly. -/
theorem canonicalPositiveTransverseReesFamily_hessianDefect_zero
    {Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hDelta : 0 < Delta)
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta)
    (h : HasCanonicalPositiveTransverseReesCoefficientBound Delta P) :
    HasPolynomialFamilyHessianDefect (K := K)
      (canonicalPositiveTransverseReesFamily Delta P h) 0 := by
  have hnonneg :
      4 * (2 * Delta) ≤
        2 * Delta +
          2 * ∑ i : Fin 4, canonicalPositiveTransverseReesWeight Delta i := by
    rw [canonicalPositiveTransverseReesWeight_sum]
    omega
  have hout :=
    adaptiveSmithFirstContactExposureFamily_hasHessianDefect
      2 (canonicalPositiveTransverseReesWeight Delta) (2 * Delta) Delta
      (by norm_num) hnonneg P h.integralExposure hdef
  change HasPolynomialFamilyHessianDefect (K := K)
    (adaptiveSmithExposureFamily
      2 (canonicalPositiveTransverseReesWeight Delta) (2 * Delta)
      P h.integralExposure) 0
  convert hout using 1
  rw [canonicalPositiveTransverseReesWeight_sum]
  omega

/-- A concrete coefficient which prevents the determinant-closing Rees
transform. -/
structure CanonicalPositiveTransverseReesLowLayer
    (Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K)) where
  exponent : Fin 4 →₀ ℕ
  mem : exponent ∈ P.support
  early :
    2 * smithFamilyCoefficientOrder P exponent +
        Finsupp.weight
          (canonicalPositiveTransverseReesWeight Delta) exponent <
      2 * Delta
  transverseDegree_le_one : canonicalTransverseDegree exponent ≤ 1
  pattern :
    IsPureLongitudinalSmithPattern
        (smithSupportExponentOf (1 : Fin 4) 2 3 exponent) ∨
      IsLowNegativeFirstSmithPattern
        (smithSupportExponentOf (1 : Fin 4) 2 3 exponent) ∨
      IsLowNegativeSecondSmithPattern
        (smithSupportExponentOf (1 : Fin 4) 2 3 exponent) ∨
      IsWLinearSmithPattern
        (smithSupportExponentOf (1 : Fin 4) 2 3 exponent)

/-- Failure of Rees coefficient integrality is necessarily one of the four
historical low Smith patterns. -/
theorem canonicalPositiveTransverseReesLowLayer_of_not_bound
    {Delta : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hDelta : 0 < Delta)
    (hnot : ¬ HasCanonicalPositiveTransverseReesCoefficientBound Delta P) :
    Nonempty (CanonicalPositiveTransverseReesLowLayer Delta P) := by
  classical
  unfold HasCanonicalPositiveTransverseReesCoefficientBound at hnot
  push_neg at hnot
  rcases hnot with ⟨d, hd, hearly⟩
  have hdegree : canonicalTransverseDegree d ≤ 1 := by
    by_contra hbad
    have htwo : 2 ≤ canonicalTransverseDegree d := by omega
    have hmul :
        2 * Delta ≤ Delta * canonicalTransverseDegree d := by
      have hm := Nat.mul_le_mul_left Delta htwo
      simpa [Nat.mul_comm] using hm
    have hweight :
        2 * Delta ≤
          Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d := by
      rw [canonicalPositiveTransverseReesWeight_finsupp]
      exact hmul
    have htotal :
        2 * Delta ≤
          2 * smithFamilyCoefficientOrder P d +
            Finsupp.weight (canonicalPositiveTransverseReesWeight Delta) d := by
      omega
    exact (Nat.not_lt_of_ge htotal) hearly
  have hcoords :
      (d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 0) ∨
      (d 1 = 0 ∧ d 2 = 1 ∧ d 3 = 0) ∨
      (d 1 = 1 ∧ d 2 = 0 ∧ d 3 = 0) ∨
      (d 1 = 0 ∧ d 2 = 0 ∧ d 3 = 1) := by
    dsimp [canonicalTransverseDegree] at hdegree
    omega
  have hpattern :
      IsPureLongitudinalSmithPattern
          (smithSupportExponentOf (1 : Fin 4) 2 3 d) ∨
        IsLowNegativeFirstSmithPattern
          (smithSupportExponentOf (1 : Fin 4) 2 3 d) ∨
        IsLowNegativeSecondSmithPattern
          (smithSupportExponentOf (1 : Fin 4) 2 3 d) ∨
        IsWLinearSmithPattern
          (smithSupportExponentOf (1 : Fin 4) 2 3 d) := by
    rcases hcoords with h0 | h1 | h2 | h3
    · left
      simpa [IsPureLongitudinalSmithPattern, smithSupportExponentOf] using h0
    · right; left
      simpa [IsLowNegativeFirstSmithPattern, smithSupportExponentOf] using h1
    · right; right; left
      simpa [IsLowNegativeSecondSmithPattern, smithSupportExponentOf] using h2
    · right; right; right
      simpa [IsWLinearSmithPattern, smithSupportExponentOf] using h3
  exact ⟨{
    exponent := d
    mem := hd
    early := hearly
    transverseDegree_le_one := hdegree
    pattern := hpattern
  }⟩

/-- **A19.17 coefficient frontier.**

At positive clock, either a concrete low Smith layer appears before the
canonical determinant-closing scale, or the transverse Rees family is an
honest polynomial family of raw Hessian defect zero. -/
theorem canonicalPositiveTransverseRees_lowLayer_or_zeroDefectFamily
    {Delta : ℕ}
    (hDelta : 0 < Delta)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    Nonempty (CanonicalPositiveTransverseReesLowLayer Delta P) ∨
      ∃ h : HasCanonicalPositiveTransverseReesCoefficientBound Delta P,
        HasPolynomialFamilyHessianDefect (K := K)
          (canonicalPositiveTransverseReesFamily Delta P h) 0 := by
  classical
  by_cases hbound : HasCanonicalPositiveTransverseReesCoefficientBound Delta P
  · right
    exact ⟨hbound,
      canonicalPositiveTransverseReesFamily_hessianDefect_zero
        hDelta hdef hbound⟩
  · left
    exact canonicalPositiveTransverseReesLowLayer_of_not_bound hDelta hbound

end

end HC4.Valuation
