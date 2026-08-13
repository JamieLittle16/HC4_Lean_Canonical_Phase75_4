import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerDirectTest
import Mathlib.Tactic

/-!
# Exact quadratic support dichotomy at direct rank-one closing

The green first-actual-layer analysis gives `j ≤ Delta`.  If equality holds,
the first actual source layer already changes the source-origin Hessian, so
some genuine quadratic source coefficient is nonzero at order `j`.

At the globally least positive actual layer there are only two possibilities
for that *same quadratic monomial*:

* its source coefficient has exact parameter order `j`, equivalently the
  quadratic monomial is fresh relative to the special fibre; or
* its source coefficient has parameter order zero, equivalently the same
  quadratic monomial is already present in the special fibre and its
  coefficient changes at order `j`.

Thus direct closing is reduced to a fresh-quadratic first-contact branch or
an overlap-quadratic deformation branch.  This is stronger than the global
fresh/overlap support split because it follows the particular quadratic
monomial which is forced by determinant closure.

No JC2 input occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- A quadratic exponent built from two source coordinates. -/
def directClosingQuadraticExponent (i k : Fin 4) : Fin 4 →₀ ℕ :=
  Finsupp.single k 1 + Finsupp.single i 1

/-- Direct closing through a genuinely fresh quadratic source monomial. -/
def HasFreshDirectClosingQuadratic
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop :=
  ∃ i k : Fin 4,
    let d := directClosingQuadraticExponent i k
    (MvPolynomial.coeff d C.family).coeff C.firstActualLayerOrder ≠ 0 ∧
      d ∉ (polynomialFamilySpecialFiber C.family).support ∧
      smithFamilyCoefficientOrder C.family d = C.firstActualLayerOrder

/-- Direct closing by changing the coefficient of a quadratic monomial which
already occurs in the old special fibre. -/
def HasOverlapDirectClosingQuadratic
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop :=
  ∃ i k : Fin 4,
    let d := directClosingQuadraticExponent i k
    (MvPolynomial.coeff d C.family).coeff C.firstActualLayerOrder ≠ 0 ∧
      d ∈ (polynomialFamilySpecialFiber C.family).support ∧
      smithFamilyCoefficientOrder C.family d = 0

/-- A coefficient which is nonzero at an actual parameter layer is an honest
source-support coefficient of the full family. -/
theorem mem_family_support_of_coeff_at_ne_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {d : Fin 4 →₀ ℕ} {n : ℕ}
    (hcoeff : (MvPolynomial.coeff d C.family).coeff n ≠ 0) :
    d ∈ C.family.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hzero
  rw [hzero] at hcoeff
  simp at hcoeff

/-- Freshness of one selected first-layer coefficient is equivalent to zero
constant coefficient of that source coefficient. -/
theorem firstActualLayer_fresh_coeff_zero
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {d : Fin 4 →₀ ℕ}
    (hfresh : d ∉ (polynomialFamilySpecialFiber C.family).support) :
    (MvPolynomial.coeff d C.family).coeff 0 = 0 := by
  have hzero :
      MvPolynomial.coeff d (polynomialFamilySpecialFiber C.family) = 0 := by
    by_contra hne
    exact hfresh (MvPolynomial.mem_support_iff.mpr hne)
  rw [coeff_polynomialFamilySpecialFiber] at hzero
  simpa [Polynomial.constantCoeff] using hzero

/-- Conversely, overlap support gives a genuinely nonzero old constant
coefficient. -/
theorem firstActualLayer_overlap_coeff_zero_ne
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {d : Fin 4 →₀ ℕ}
    (hoverlap : d ∈ (polynomialFamilySpecialFiber C.family).support) :
    (MvPolynomial.coeff d C.family).coeff 0 ≠ 0 := by
  have hne :
      MvPolynomial.coeff d (polynomialFamilySpecialFiber C.family) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hoverlap
  rw [coeff_polynomialFamilySpecialFiber] at hne
  simpa [Polynomial.constantCoeff] using hne

/-- **Quadratic support dichotomy at direct closing.**

If `j = Delta`, follow one quadratic coefficient whose order-`j` term is
forced by the Hessian determinant clock.  Minimality of `j` says the exact
parameter order of this same coefficient is either `j` or zero.  These are
precisely the fresh and overlap alternatives. -/
theorem directClosing_freshQuadratic_or_overlapQuadratic
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) :
    C.HasFreshDirectClosingQuadratic ∨ C.HasOverlapDirectClosingQuadratic := by
  rcases C.firstActualLayer_hasQuadraticSourceCoefficient_of_eq_defect heq with
    ⟨i, k, hcoeff⟩
  let d := directClosingQuadraticExponent i k
  have hd : d ∈ C.family.support := by
    apply C.mem_family_support_of_coeff_at_ne_zero (d := d)
    simpa [d, directClosingQuadraticExponent] using hcoeff
  have hsplit :=
    smithFamilyCoefficientParameterOrder_zero_or_firstPositiveActual
      C.family C.hasPositiveActualParameterLayer hd hcoeff
  rcases hsplit with hzero | hfirst
  · right
    refine ⟨i, k, ?_, ?_, ?_⟩
    · simpa [d, directClosingQuadraticExponent] using hcoeff
    · apply
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
          C.family hd).1
      rw [smithFamilyCoefficientOrder_eq C.family hd]
      exact hzero
    · rw [smithFamilyCoefficientOrder_eq C.family hd]
      exact hzero
  · left
    have hfresh :
        d ∉ (polynomialFamilySpecialFiber C.family).support := by
      intro hspecial
      have hz : smithFamilyCoefficientOrder C.family d = 0 :=
        (smithFamilyCoefficientOrder_eq_zero_iff_mem_specialFiber
          C.family hd).2 hspecial
      rw [smithFamilyCoefficientOrder_eq C.family hd, hfirst] at hz
      exact (Nat.ne_of_gt C.firstActualLayerOrder_pos) hz
    refine ⟨i, k, ?_, ?_, ?_⟩
    · simpa [d, directClosingQuadraticExponent] using hcoeff
    · simpa [d] using hfresh
    · rw [smithFamilyCoefficientOrder_eq C.family hd]
      exact hfirst

/-- Fresh direct closing has an actual quadratic coefficient which is absent
at parameter zero and whose exact parameter order is the closing defect. -/
theorem freshDirectClosingQuadratic_exactOrder_defect
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (h : C.HasFreshDirectClosingQuadratic) :
    ∃ i k : Fin 4,
      let d := directClosingQuadraticExponent i k
      (MvPolynomial.coeff d C.family).coeff 0 = 0 ∧
      (MvPolynomial.coeff d C.family).coeff B.aligned.endpoint.defect ≠ 0 ∧
      smithFamilyCoefficientOrder C.family d = B.aligned.endpoint.defect := by
  rcases h with ⟨i, k, hcoeff, hfresh, horder⟩
  refine ⟨i, k, ?_, ?_, ?_⟩
  · exact C.firstActualLayer_fresh_coeff_zero hfresh
  · simpa [heq] using hcoeff
  · simpa [heq] using horder

/-- Overlap direct closing changes a quadratic coefficient which was already
nonzero on the old special fibre.  Thus both its constant term and its
closing-order coefficient are nonzero. -/
theorem overlapDirectClosingQuadratic_twoVisibleLayers
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (h : C.HasOverlapDirectClosingQuadratic) :
    ∃ i k : Fin 4,
      let d := directClosingQuadraticExponent i k
      (MvPolynomial.coeff d C.family).coeff 0 ≠ 0 ∧
      (MvPolynomial.coeff d C.family).coeff B.aligned.endpoint.defect ≠ 0 ∧
      smithFamilyCoefficientOrder C.family d = 0 := by
  rcases h with ⟨i, k, hcoeff, hoverlap, horder⟩
  refine ⟨i, k, ?_, ?_, ?_⟩
  · exact C.firstActualLayer_overlap_coeff_zero_ne hoverlap
  · simpa [heq] using hcoeff
  · exact horder

/-- Complete timing/support frontier after the direct quadratic test. -/
theorem firstActualLayer_strict_or_directQuadraticSupport
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    (C.firstActualLayerOrder < B.aligned.endpoint.defect ∧
      C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder) ∨
    (C.firstActualLayerOrder = B.aligned.endpoint.defect ∧
      (C.HasFreshDirectClosingQuadratic ∨
       C.HasOverlapDirectClosingQuadratic)) := by
  rcases C.firstActualLayer_preclosing_or_directQuadratic with hpre | hclose
  · exact Or.inl hpre
  · exact Or.inr
      ⟨hclose.1,
        C.directClosing_freshQuadratic_or_overlapQuadratic hclose.1⟩

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
