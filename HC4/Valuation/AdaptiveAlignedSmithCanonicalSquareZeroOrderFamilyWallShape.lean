import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingSectionGauge
import Mathlib.Tactic

/-!
# Zero-order family shape at the canonical square equality spill

The sharp `j = Delta` wall normal form has already separated positive section
walls from family walls.  Positive section walls are honest pointed gauge
steps.  Every remaining family wall has exact parameter order zero, hence is
already present in the special fibre.

This file records the finite support consequence of the canonical square
weight at such a zero-order wall.

* for a longitudinal square (`index = 0`), the offending special-fibre
  monomial has total transverse degree at most one;
* for a transverse square (`index != 0`), its total degree in the two
  coordinates complementary to the marked axis and square axis is at most
  one.

Thus the equality spill is no longer an unspecified earlier clock: it is
exactly either a source-equivalent positive pointed gauge step or a concrete
low-transverse-degree special-fibre wall.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped BigOperators

universe u

variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- Degree in the two coordinates complementary to the marked longitudinal
axis `0` and a transverse square axis `ell`. -/
def directClosingTransverseComplementDegree
    (ell : Fin 4) (d : Fin 4 →₀ ℕ) : ℕ :=
  ∑ k : Fin 4, if k = (0 : Fin 4) ∨ k = ell then 0 else d k

/-- For a genuinely transverse square, the canonical square weight is exactly
`3*Delta` times complementary degree. -/
theorem directClosingCanonicalSquareWeight_transverse
    (Delta : ℕ) (ell : Fin 4) (hell : ell ≠ (0 : Fin 4))
    (d : Fin 4 →₀ ℕ) :
    Finsupp.weight (directClosingCanonicalSquareWeight Delta ell) d =
      3 * Delta * directClosingTransverseComplementDegree ell d := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · fin_cases ell
    · exact (hell rfl).elim
    · simp [directClosingCanonicalSquareWeight,
        directClosingTransverseComplementDegree, Fin.sum_univ_four]
      ring
    · simp [directClosingCanonicalSquareWeight,
        directClosingTransverseComplementDegree, Fin.sum_univ_four]
      ring
    · simp [directClosingCanonicalSquareWeight,
        directClosingTransverseComplementDegree, Fin.sum_univ_four]
      ring
  · intro i
    simp

/-- Exact parameter order zero means that a supported family monomial really
belongs to the special fibre. -/
theorem DirectClosingAlignedSquareSourceData.mem_specialFiber_support_of_order_zero
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : DirectClosingAlignedSquareSourceData C)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ D.family.support)
    (horder0 : smithFamilyCoefficientParameterOrder D.family d hd = 0) :
    d ∈ (polynomialFamilySpecialFiber D.family).support := by
  rw [MvPolynomial.mem_support_iff, coeff_polynomialFamilySpecialFiber]
  have hc : MvPolynomial.coeff d D.family ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hne := polynomialParameterOrder_coeff_ne_zero
    (MvPolynomial.coeff d D.family) hc
  have horder :
      polynomialParameterOrder (MvPolynomial.coeff d D.family) hc = 0 := by
    simpa [smithFamilyCoefficientParameterOrder] using horder0
  change (MvPolynomial.coeff d D.family).coeff 0 ≠ 0
  simpa [horder] using hne

/-- A longitudinal zero-order canonical family wall is affine in total
transverse degree at its offending monomial. -/
theorem zeroOrderCanonicalFamilyWall_longitudinal_degree_le_one
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (D : DirectClosingAlignedSquareSourceData C)
    (hindex : D.index = (0 : Fin 4))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ D.family.support)
    (hlt :
      directClosingCanonicalSquareRamification *
            smithFamilyCoefficientParameterOrder D.family d hd +
          Finsupp.weight
            (directClosingCanonicalSquareWeight
              B.aligned.endpoint.defect D.index) d <
        directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
    (horder0 : smithFamilyCoefficientParameterOrder D.family d hd = 0) :
    directClosingLongitudinalTransverseDegree d ≤ 1 := by
  have hDelta : 0 < B.aligned.endpoint.defect := by
    rw [← heq]
    exact C.firstActualLayerOrder_pos
  have hweight :
      Finsupp.weight
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index) d <
        4 * B.aligned.endpoint.defect := by
    simpa [directClosingCanonicalSquareRamification,
      directClosingCanonicalSquareCommonLevel, horder0] using hlt
  rw [hindex, directClosingCanonicalSquareWeight_longitudinal] at hweight
  by_contra hnot
  have hdeg : 2 ≤ directClosingLongitudinalTransverseDegree d := by omega
  have hmul :
      (2 * B.aligned.endpoint.defect) * 2 ≤
        (2 * B.aligned.endpoint.defect) *
          directClosingLongitudinalTransverseDegree d :=
    Nat.mul_le_mul_left (2 * B.aligned.endpoint.defect) hdeg
  have h4 :
      4 * B.aligned.endpoint.defect ≤
        2 * B.aligned.endpoint.defect *
          directClosingLongitudinalTransverseDegree d := by
    calc
      4 * B.aligned.endpoint.defect =
          (2 * B.aligned.endpoint.defect) * 2 := by ring
      _ ≤ _ := hmul
  omega

/-- A transverse zero-order canonical family wall is affine in the two
coordinates complementary to `0` and the square axis at its offending
monomial. -/
theorem zeroOrderCanonicalFamilyWall_transverse_degree_le_one
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect)
    (D : DirectClosingAlignedSquareSourceData C)
    (hindex : D.index ≠ (0 : Fin 4))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ D.family.support)
    (hlt :
      directClosingCanonicalSquareRamification *
            smithFamilyCoefficientParameterOrder D.family d hd +
          Finsupp.weight
            (directClosingCanonicalSquareWeight
              B.aligned.endpoint.defect D.index) d <
        directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
    (horder0 : smithFamilyCoefficientParameterOrder D.family d hd = 0) :
    directClosingTransverseComplementDegree D.index d ≤ 1 := by
  have hDelta : 0 < B.aligned.endpoint.defect := by
    rw [← heq]
    exact C.firstActualLayerOrder_pos
  have hweight :
      Finsupp.weight
          (directClosingCanonicalSquareWeight
            B.aligned.endpoint.defect D.index) d <
        4 * B.aligned.endpoint.defect := by
    simpa [directClosingCanonicalSquareRamification,
      directClosingCanonicalSquareCommonLevel, horder0] using hlt
  rw [directClosingCanonicalSquareWeight_transverse
      B.aligned.endpoint.defect D.index hindex d] at hweight
  by_contra hnot
  have hdeg : 2 ≤ directClosingTransverseComplementDegree D.index d := by omega
  have hmul :
      (3 * B.aligned.endpoint.defect) * 2 ≤
        (3 * B.aligned.endpoint.defect) *
          directClosingTransverseComplementDegree D.index d :=
    Nat.mul_le_mul_left (3 * B.aligned.endpoint.defect) hdeg
  have h6 :
      6 * B.aligned.endpoint.defect ≤
        3 * B.aligned.endpoint.defect *
          directClosingTransverseComplementDegree D.index d := by
    calc
      6 * B.aligned.endpoint.defect =
          (3 * B.aligned.endpoint.defect) * 2 := by ring
      _ ≤ _ := hmul
  have h46 :
      4 * B.aligned.endpoint.defect < 6 * B.aligned.endpoint.defect := by
    omega
  omega

/-- Complete source-honest shape of a zero-order family wall.  The original
family/support/wall evidence is retained together with special-fibre support
and the sharp low-degree conclusion. -/
inductive DirectClosingCanonicalSquareZeroOrderFamilyWallShape
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop
  | longitudinal
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index = (0 : Fin 4))
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ D.family.support)
      (hlt :
        directClosingCanonicalSquareRamification *
              smithFamilyCoefficientParameterOrder D.family d hd +
            Finsupp.weight
              (directClosingCanonicalSquareWeight
                B.aligned.endpoint.defect D.index) d <
          directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
      (horder0 : smithFamilyCoefficientParameterOrder D.family d hd = 0)
      (hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support)
      (hdegree : directClosingLongitudinalTransverseDegree d ≤ 1)
  | transverse
      (D : DirectClosingAlignedSquareSourceData C)
      (hindex : D.index ≠ (0 : Fin 4))
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ D.family.support)
      (hlt :
        directClosingCanonicalSquareRamification *
              smithFamilyCoefficientParameterOrder D.family d hd +
            Finsupp.weight
              (directClosingCanonicalSquareWeight
                B.aligned.endpoint.defect D.index) d <
          directClosingCanonicalSquareCommonLevel B.aligned.endpoint.defect)
      (horder0 : smithFamilyCoefficientParameterOrder D.family d hd = 0)
      (hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support)
      (hdegree : directClosingTransverseComplementDegree D.index d ≤ 1)

/-- The equality spill after pointed section gauge normalisation has only two
honest outputs: a low-degree special-fibre family wall, or a positive pointed
source-gauge step. -/
inductive DirectClosingCanonicalSquareEqualityReducedFrontier
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (heq : C.firstActualLayerOrder = B.aligned.endpoint.defect) : Prop
  | zeroOrderFamily
      (Z : DirectClosingCanonicalSquareZeroOrderFamilyWallShape C heq)
  | sectionGauge
      (G : DirectClosingPositiveSectionGaugeStep C)

/-- Consume the sharp equality-wall/gauge frontier into the reduced two-way
shape above. -/
theorem DirectClosingCanonicalSquareEarlierWallNormalForm.toReducedFrontier
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {heq : C.firstActualLayerOrder = B.aligned.endpoint.defect}
    (N : DirectClosingCanonicalSquareEarlierWallNormalForm C heq) :
    DirectClosingCanonicalSquareEqualityReducedFrontier C heq := by
  have G := N.toGaugeFrontier
  cases G with
  | longitudinalFamily fresh d hd hlt horder0 =>
      let D := C.directClosingLongitudinalSquareSource fresh
      have hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support :=
        D.mem_specialFiber_support_of_order_zero d hd horder0
      have hdegree : directClosingLongitudinalTransverseDegree d ≤ 1 :=
        zeroOrderCanonicalFamilyWall_longitudinal_degree_le_one
          heq D (by rfl) d hd hlt horder0
      exact .zeroOrderFamily (.longitudinal
        D (by rfl) d hd hlt horder0 hdSpecial hdegree)
  | transverseFamily A d hd hlt horder0 =>
      let D := A.toAlignedSquareSource
      have hindex : D.index ≠ (0 : Fin 4) := by
        change A.ell ≠ (0 : Fin 4)
        exact A.ell_ne_zero
      have hdSpecial : d ∈ (polynomialFamilySpecialFiber D.family).support :=
        D.mem_specialFiber_support_of_order_zero d hd horder0
      have hdegree : directClosingTransverseComplementDegree D.index d ≤ 1 :=
        zeroOrderCanonicalFamilyWall_transverse_degree_le_one
          heq D hindex d hd hlt horder0
      exact .zeroOrderFamily (.transverse
        D hindex d hd hlt horder0 hdSpecial hdegree)
  | sectionGauge G =>
      exact .sectionGauge G

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
