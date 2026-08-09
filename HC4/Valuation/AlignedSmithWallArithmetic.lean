import HC4.Valuation.ZeroSlopeSmithDispatcher
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Exact parameter order and aligned symmetric Smith walls

Phase 93.65 closes the genuine one-step Smith dispatcher but deliberately
leaves the global scale issue visible.  The symmetric Smith direction has
extra arithmetic structure that lets us remove rational wall positions
entirely.

For the canonical separator `(k,l)=(1,1)`,

    delta(e) = 2 * (b + c + 2d - 2).

Hence `delta` is even.  The universal lower bound `delta >= -4` therefore
shows that the only negative derivatives are

    -4, -2.

After one ramification by `20`, every negative coefficient wall occurs at
an integer Smith step:

    20*v + N*(-4) = 0  at N = 5*v,
    20*v + N*(-2) = 0  at N = 10*v.

The marked sections align on the same lattice:

    20*v - 2*N = 0  at N = 10*v   (y,z),
    20*v - 4*N = 0  at N = 5*v    (w).

Thus the maximal legal symmetric tilt can be selected from natural numbers
after a single fixed ramification, without iterated denominator clearing.

This file also extracts the exact `X`-adic order of every nonzero
univariate polynomial by the same finite-maximum method used successfully
for the maximal kernel slope in Phase 93.58.  That order is the concrete
input for the wall selector.

No global restart theorem is claimed here; this is the exact arithmetic and
order-extraction layer required for the maximal-wall construction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Exact X-adic order of a nonzero polynomial -/

/-- Every `X^n` dividing a nonzero polynomial has exponent at most its
ordinary degree. -/
theorem polynomial_X_pow_dvd_le_natDegree
    (c : Polynomial K)
    (hc : c ≠ 0)
    (n : ℕ)
    (hdiv : Polynomial.X ^ n ∣ c) :
    n ≤ c.natDegree := by
  rcases hdiv with ⟨r, hr⟩
  have hrne : r ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hr
    exact hc hr
  have hpowne :
      (Polynomial.X ^ n : Polynomial K) ≠ 0 :=
    pow_ne_zero n Polynomial.X_ne_zero
  have hdeg :
      c.natDegree = n + r.natDegree := by
    rw [hr]
    simpa using
      (Polynomial.natDegree_mul hpowne hrne)
  omega

/-- Finite set of all powers of `X` dividing a fixed nonzero polynomial. -/
noncomputable def polynomialParameterOrderCandidates
    (c : Polynomial K)
    (hc : c ≠ 0) :
    Finset ℕ := by
  classical
  exact
    (Finset.range (c.natDegree + 1)).filter
      (fun n => Polynomial.X ^ n ∣ c)

/-- `0` is always an admissible parameter order. -/
theorem zero_mem_polynomialParameterOrderCandidates
    (c : Polynomial K)
    (hc : c ≠ 0) :
    0 ∈ polynomialParameterOrderCandidates c hc := by
  classical
  simp [polynomialParameterOrderCandidates]

/-- The order-candidate set is nonempty. -/
theorem polynomialParameterOrderCandidates_nonempty
    (c : Polynomial K)
    (hc : c ≠ 0) :
    (polynomialParameterOrderCandidates c hc).Nonempty := by
  exact
    ⟨0,
      zero_mem_polynomialParameterOrderCandidates
        c hc⟩

/-- Exact `X`-adic vanishing order of a nonzero polynomial. -/
noncomputable def polynomialParameterOrder
    (c : Polynomial K)
    (hc : c ≠ 0) :
    ℕ :=
  (polynomialParameterOrderCandidates c hc).max'
    (polynomialParameterOrderCandidates_nonempty c hc)

/-- The selected exact order is itself admissible. -/
theorem polynomialParameterOrder_mem
    (c : Polynomial K)
    (hc : c ≠ 0) :
    polynomialParameterOrder c hc ∈
      polynomialParameterOrderCandidates c hc := by
  unfold polynomialParameterOrder
  exact
    Finset.max'_mem
      (polynomialParameterOrderCandidates c hc)
      (polynomialParameterOrderCandidates_nonempty c hc)

/-- The selected exact parameter power divides the polynomial. -/
theorem polynomialParameterOrder_dvd
    (c : Polynomial K)
    (hc : c ≠ 0) :
    Polynomial.X ^ (polynomialParameterOrder c hc) ∣ c := by
  classical
  have hmem :=
    polynomialParameterOrder_mem c hc
  have hmem' :
      polynomialParameterOrder c hc < c.natDegree + 1 ∧
        Polynomial.X ^ (polynomialParameterOrder c hc) ∣ c := by
    simpa [polynomialParameterOrderCandidates] using hmem
  exact hmem'.2

/-- Every other admissible `X`-power is at most the selected order. -/
theorem polynomial_X_pow_dvd_le_parameterOrder
    (c : Polynomial K)
    (hc : c ≠ 0)
    (n : ℕ)
    (hdiv : Polynomial.X ^ n ∣ c) :
    n ≤ polynomialParameterOrder c hc := by
  have hbound :=
    polynomial_X_pow_dvd_le_natDegree c hc n hdiv
  have hmem :
      n ∈ polynomialParameterOrderCandidates c hc := by
    classical
    simp [polynomialParameterOrderCandidates,
      Nat.lt_succ_iff.mpr hbound, hdiv]
  unfold polynomialParameterOrder
  exact
    Finset.le_max'
      (polynomialParameterOrderCandidates c hc)
      n hmem

/-- Exactness: the next parameter power does not divide. -/
theorem polynomialParameterOrder_succ_not_dvd
    (c : Polynomial K)
    (hc : c ≠ 0) :
    ¬ Polynomial.X ^ (polynomialParameterOrder c hc + 1) ∣ c := by
  intro hsucc
  have hle :=
    polynomial_X_pow_dvd_le_parameterOrder
      c hc
      (polynomialParameterOrder c hc + 1)
      hsucc
  omega

/-- Chosen primitive quotient after removing the exact parameter order. -/
noncomputable def polynomialParameterPrimitivePart
    (c : Polynomial K)
    (hc : c ≠ 0) :
    Polynomial K :=
  Classical.choose
    (polynomialParameterOrder_dvd c hc)

/-- Exact factorisation into parameter order and primitive part. -/
theorem polynomialParameterPrimitivePart_spec
    (c : Polynomial K)
    (hc : c ≠ 0) :
    c =
      Polynomial.X ^ (polynomialParameterOrder c hc) *
        polynomialParameterPrimitivePart c hc := by
  exact
    Classical.choose_spec
      (polynomialParameterOrder_dvd c hc)

/-- The primitive part really has nonzero special value. -/
theorem polynomialParameterPrimitivePart_constantCoeff_ne_zero
    (c : Polynomial K)
    (hc : c ≠ 0) :
    Polynomial.constantCoeff
        (polynomialParameterPrimitivePart c hc) ≠ 0 := by
  intro hzero
  have hXd :
      Polynomial.X ∣
        polynomialParameterPrimitivePart c hc := by
    rw [Polynomial.X_dvd_iff]
    exact hzero
  rcases hXd with ⟨r, hr⟩
  apply
    polynomialParameterOrder_succ_not_dvd c hc
  refine ⟨r, ?_⟩
  calc
    c =
        Polynomial.X ^ (polynomialParameterOrder c hc) *
          polynomialParameterPrimitivePart c hc :=
      polynomialParameterPrimitivePart_spec c hc
    _ =
        Polynomial.X ^ (polynomialParameterOrder c hc) *
          (Polynomial.X * r) := by rw [hr]
    _ =
        Polynomial.X ^
            (polynomialParameterOrder c hc + 1) *
          r := by
            rw [pow_succ]
            ring

/-! ## Exact order of genuine family coefficients -/

/-- Exact parameter order of a source coefficient known to lie in support. -/
noncomputable def smithFamilyCoefficientParameterOrder
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support) :
    ℕ :=
  polynomialParameterOrder
    (MvPolynomial.coeff d P)
    (MvPolynomial.mem_support_iff.mp hd)

/-- The exact family coefficient order gives the required divisibility. -/
theorem smithFamilyCoefficientParameterOrder_dvd
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support) :
    Polynomial.X ^
        (smithFamilyCoefficientParameterOrder P d hd) ∣
      MvPolynomial.coeff d P := by
  exact
    polynomialParameterOrder_dvd
      (MvPolynomial.coeff d P)
      (MvPolynomial.mem_support_iff.mp hd)

/-- The primitive coefficient left after exact order extraction has nonzero
constant coefficient. -/
theorem smithFamilyCoefficientPrimitive_constantCoeff_ne_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ P.support) :
    Polynomial.constantCoeff
        (polynomialParameterPrimitivePart
          (MvPolynomial.coeff d P)
          (MvPolynomial.mem_support_iff.mp hd)) ≠ 0 := by
  exact
    polynomialParameterPrimitivePart_constantCoeff_ne_zero
      (MvPolynomial.coeff d P)
      (MvPolynomial.mem_support_iff.mp hd)

/-! ## Exact symmetric Smith derivative arithmetic -/

/-- Closed formula for the canonical symmetric Smith derivative. -/
theorem smithSeparatorDelta_one_one_formula
    (e : SmithSupportExponent) :
    smithSeparatorDelta 1 1 e =
      2 *
        ((e.b : ℤ) + (e.c : ℤ) +
          2 * (e.d : ℤ) - 2) := by
  unfold smithSeparatorDelta
  rw [HC4.Newton.smithExtremeSeparator_one_one]
  unfold SmithSupportExponent.grade
  unfold smithGradeDot
  unfold smithGrade
  unfold smithGradeFirst
  unfold smithGradeSecond
  push_cast
  ring

/-- In particular the symmetric Smith derivative is always even. -/
theorem smithSeparatorDelta_one_one_even
    (e : SmithSupportExponent) :
    ∃ z : ℤ,
      smithSeparatorDelta 1 1 e = 2 * z := by
  refine
    ⟨(e.b : ℤ) + (e.c : ℤ) +
      2 * (e.d : ℤ) - 2, ?_⟩
  exact smithSeparatorDelta_one_one_formula e

/-- The only negative symmetric Smith derivatives are `-4` and `-2`. -/
theorem smithSeparatorDelta_one_one_negative_cases
    (e : SmithSupportExponent)
    (hneg : smithSeparatorDelta 1 1 e < 0) :
    smithSeparatorDelta 1 1 e = -4 ∨
      smithSeparatorDelta 1 1 e = -2 := by
  have hlower :
      (-4 : ℤ) ≤ smithSeparatorDelta 1 1 e := by
    simpa [HC4.Newton.smithExtremeSeparatorBound_one_one] using
      (smithSeparatorDelta_lower_bound 1 1 e)
  rcases smithSeparatorDelta_one_one_even e with
    ⟨z, hz⟩
  rw [hz] at hneg hlower
  have hzrange :
      z = -2 ∨ z = -1 := by
    omega
  rcases hzrange with rfl | rfl
  · left
    simpa using hz
  · right
    simpa using hz

/-! ## Ramification 20 aligns every possible wall -/

/-- Single ramification index used by the maximal symmetric wall
construction. -/
def alignedSmithRamificationIndex : ℕ := 20

theorem alignedSmithRamificationIndex_pos :
    0 < alignedSmithRamificationIndex := by
  norm_num [alignedSmithRamificationIndex]

/-- Denominator `10` from the small Smith tilt divides the aligned
ramification index `20`. -/
theorem smithSeparatorRamificationIndex_dvd_aligned :
    HC4.Valuation.smithSeparatorRamificationIndex 1 1 ∣
      alignedSmithRamificationIndex := by
  rw [HC4.Newton.smithSeparatorRamificationIndex_one_one]
  norm_num [alignedSmithRamificationIndex]

/-- Parameter-order contribution after ramification by twenty and `N`
integer symmetric Smith steps. -/
def alignedSmithCoefficientValue
    (v N : ℕ)
    (delta : ℤ) : ℤ :=
  (alignedSmithRamificationIndex : ℤ) * (v : ℤ) +
    (N : ℤ) * delta

/-- A derivative `-4` hits its coefficient wall exactly at step `5*v`. -/
theorem alignedSmithCoefficientValue_neg_four_wall
    (v : ℕ) :
    alignedSmithCoefficientValue v (5 * v) (-4) = 0 := by
  unfold alignedSmithCoefficientValue
  norm_num [alignedSmithRamificationIndex]
  ring

/-- Before the `-4` wall the aligned coefficient value is nonnegative. -/
theorem alignedSmithCoefficientValue_neg_four_nonnegative
    (v N : ℕ)
    (hN : N ≤ 5 * v) :
    0 ≤ alignedSmithCoefficientValue v N (-4) := by
  unfold alignedSmithCoefficientValue
  norm_num [alignedSmithRamificationIndex]
  omega

/-- A derivative `-2` hits its coefficient wall exactly at step `10*v`. -/
theorem alignedSmithCoefficientValue_neg_two_wall
    (v : ℕ) :
    alignedSmithCoefficientValue v (10 * v) (-2) = 0 := by
  unfold alignedSmithCoefficientValue
  norm_num [alignedSmithRamificationIndex]
  ring

/-- Before the `-2` wall the aligned coefficient value is nonnegative. -/
theorem alignedSmithCoefficientValue_neg_two_nonnegative
    (v N : ℕ)
    (hN : N ≤ 10 * v) :
    0 ≤ alignedSmithCoefficientValue v N (-2) := by
  unfold alignedSmithCoefficientValue
  norm_num [alignedSmithRamificationIndex]
  omega

/-- Nonnegative Smith derivative never obstructs coefficient integrality on
the aligned scale. -/
theorem alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
    (v N : ℕ)
    (delta : ℤ)
    (hdelta : 0 ≤ delta) :
    0 ≤ alignedSmithCoefficientValue v N delta := by
  unfold alignedSmithCoefficientValue
  have hv :
      (0 : ℤ) ≤
        (alignedSmithRamificationIndex : ℤ) * (v : ℤ) := by
    positivity
  have hN :
      (0 : ℤ) ≤ (N : ℤ) * delta := by
    positivity
  omega

/-- Complete aligned legality classification for a single coefficient. -/
theorem alignedSmithCoefficientValue_nonnegative_iff_cases
    (e : SmithSupportExponent)
    (v N : ℕ)
    (hneg4 :
      smithSeparatorDelta 1 1 e = -4 ->
        N ≤ 5 * v)
    (hneg2 :
      smithSeparatorDelta 1 1 e = -2 ->
        N ≤ 10 * v) :
    0 ≤
      alignedSmithCoefficientValue
        v N (smithSeparatorDelta 1 1 e) := by
  by_cases hneg :
      smithSeparatorDelta 1 1 e < 0
  · rcases
      smithSeparatorDelta_one_one_negative_cases
        e hneg with
      h4 | h2
    · rw [h4]
      exact
        alignedSmithCoefficientValue_neg_four_nonnegative
          v N (hneg4 h4)
    · rw [h2]
      exact
        alignedSmithCoefficientValue_neg_two_nonnegative
          v N (hneg2 h2)
  · have hnonneg :
        0 ≤ smithSeparatorDelta 1 1 e := by
      omega
    exact
      alignedSmithCoefficientValue_nonnegative_of_delta_nonnegative
        v N _ hnonneg

/-! ## Marked-section walls on the same integer lattice -/

/-- Aligned order of a `y` or `z` section coordinate after `N` symmetric
steps. -/
def alignedSmithSectionValueTwo
    (v N : ℕ) : ℤ :=
  (alignedSmithRamificationIndex : ℤ) * (v : ℤ) -
    2 * (N : ℤ)

/-- Aligned order of a `w` section coordinate after `N` symmetric steps. -/
def alignedSmithSectionValueFour
    (v N : ℕ) : ℤ :=
  (alignedSmithRamificationIndex : ℤ) * (v : ℤ) -
    4 * (N : ℤ)

/-- A `y`/`z` section coordinate of order `v` hits the boundary at
`N=10*v`. -/
theorem alignedSmithSectionValueTwo_wall
    (v : ℕ) :
    alignedSmithSectionValueTwo v (10 * v) = 0 := by
  unfold alignedSmithSectionValueTwo
  norm_num [alignedSmithRamificationIndex]
  ring

theorem alignedSmithSectionValueTwo_nonnegative
    (v N : ℕ)
    (hN : N ≤ 10 * v) :
    0 ≤ alignedSmithSectionValueTwo v N := by
  unfold alignedSmithSectionValueTwo
  norm_num [alignedSmithRamificationIndex]
  omega

/-- A `w` section coordinate of order `v` hits the boundary at `N=5*v`. -/
theorem alignedSmithSectionValueFour_wall
    (v : ℕ) :
    alignedSmithSectionValueFour v (5 * v) = 0 := by
  unfold alignedSmithSectionValueFour
  norm_num [alignedSmithRamificationIndex]
  ring

theorem alignedSmithSectionValueFour_nonnegative
    (v N : ℕ)
    (hN : N ≤ 5 * v) :
    0 ≤ alignedSmithSectionValueFour v N := by
  unfold alignedSmithSectionValueFour
  norm_num [alignedSmithRamificationIndex]
  omega

/-! ## Finite integer wall bound data -/

/-- Integer step at which a negative coefficient derivative hits zero.
Nonnegative derivatives carry no finite coefficient wall. -/
def alignedSmithNegativeCoefficientWall
    (e : SmithSupportExponent)
    (v : ℕ) : Option ℕ :=
  if smithSeparatorDelta 1 1 e = -4 then
    some (5 * v)
  else if smithSeparatorDelta 1 1 e = -2 then
    some (10 * v)
  else
    none

theorem alignedSmithNegativeCoefficientWall_spec
    (e : SmithSupportExponent)
    (v wall : ℕ)
    (hwall :
      alignedSmithNegativeCoefficientWall e v =
        some wall) :
    alignedSmithCoefficientValue
        v wall (smithSeparatorDelta 1 1 e) = 0 := by
  unfold alignedSmithNegativeCoefficientWall at hwall
  by_cases h4 :
      smithSeparatorDelta 1 1 e = -4
  · simp [h4] at hwall
    subst wall
    rw [h4]
    exact alignedSmithCoefficientValue_neg_four_wall v
  · simp [h4] at hwall
    by_cases h2 :
        smithSeparatorDelta 1 1 e = -2
    · simp [h2] at hwall
      subst wall
      rw [h2]
      exact alignedSmithCoefficientValue_neg_two_wall v
    · simp [h2] at hwall

/-- Every genuinely negative symmetric coefficient derivative has an
aligned finite wall. -/
theorem alignedSmithNegativeCoefficientWall_exists_of_negative
    (e : SmithSupportExponent)
    (v : ℕ)
    (hneg : smithSeparatorDelta 1 1 e < 0) :
    ∃ wall : ℕ,
      alignedSmithNegativeCoefficientWall e v =
        some wall := by
  rcases
      smithSeparatorDelta_one_one_negative_cases
        e hneg with
    h4 | h2
  · exact
      ⟨5 * v,
        by
          simp [alignedSmithNegativeCoefficientWall,
            h4]⟩
  · exact
      ⟨10 * v,
        by
          simp [alignedSmithNegativeCoefficientWall,
            h2]⟩

end

end HC4.Valuation
