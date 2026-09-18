import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreDirectionLock
import HC4.Valuation.SmithFrontierFourBlockExtraction
import Mathlib.Tactic

/-!
# Two explicit coefficients of a binary linear-form power

For L = c0*U + c1*V we record only the two coefficients needed by the final
finite-staircase adjacency argument:

* [U^m] L^m = c0^m;
* [U^m V] L^(m+1) = (m+1) c1 c0^m.

The second identity is obtained by one formal derivative in V, so no general
multinomial expansion is needed.
-/

namespace HC4.Polynomial

noncomputable section

open HC4.Valuation

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Binary pure-U exponent. -/
def binaryPureZeroExponent (m : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) m

/-- Binary adjacent exponent U^m V. -/
def binaryAdjacentZeroOneExponent (m : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) m + Finsupp.single (1 : Fin 2) 1

@[simp] theorem binaryPureZeroExponent_zero_apply
    (m : ℕ) :
    binaryPureZeroExponent m (0 : Fin 2) = m := by
  simp [binaryPureZeroExponent, Finsupp.single_apply]

@[simp] theorem binaryPureZeroExponent_one_apply
    (m : ℕ) :
    binaryPureZeroExponent m (1 : Fin 2) = 0 := by
  simp [binaryPureZeroExponent, Finsupp.single_apply]

@[simp] theorem binaryAdjacentZeroOneExponent_zero_apply
    (m : ℕ) :
    binaryAdjacentZeroOneExponent m (0 : Fin 2) = m := by
  simp [binaryAdjacentZeroOneExponent, Finsupp.single_apply]

@[simp] theorem binaryAdjacentZeroOneExponent_one_apply
    (m : ℕ) :
    binaryAdjacentZeroOneExponent m (1 : Fin 2) = 1 := by
  simp [binaryAdjacentZeroOneExponent, Finsupp.single_apply]

theorem binaryPureZeroExponent_succ
    (m : ℕ) :
    binaryPureZeroExponent (m + 1) =
      binaryPureZeroExponent m + Finsupp.single (0 : Fin 2) 1 := by
  ext i
  fin_cases i <;>
    simp [binaryPureZeroExponent, Finsupp.single_apply]

/-- The canonical binary gradient-ratio linear form is literally
c0*U + c1*V. -/
theorem gradientRatioLinearForm_finTwo_eq
    (c : Fin 2 → K) :
    gradientRatioLinearForm c =
      MvPolynomial.C (c 0) * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C (c 1) * MvPolynomial.X (1 : Fin 2) := by
  simp [gradientRatioLinearForm, Fin.sum_univ_two]

/-- Pure-U coefficient of a binary linear-form power. -/
theorem coeff_gradientRatioLinearForm_pow_pure_zero
    (c : Fin 2 → K) :
    ∀ m : ℕ,
      MvPolynomial.coeff (binaryPureZeroExponent m)
          ((gradientRatioLinearForm c) ^ m) =
        (c 0) ^ m := by
  intro m
  induction m with
  | zero =>
      simp [binaryPureZeroExponent]
  | succ m ih =>
      rw [pow_succ, gradientRatioLinearForm_finTwo_eq, mul_add,
        MvPolynomial.coeff_add]
      have htarget := binaryPureZeroExponent_succ m
      rw [show m + 1 = Nat.succ m by omega] at htarget
      rw [htarget]
      have hfirst :
          MvPolynomial.coeff
              (binaryPureZeroExponent m + Finsupp.single (0 : Fin 2) 1)
              (((gradientRatioLinearForm c) ^ m) *
                (MvPolynomial.C (c 0) * MvPolynomial.X (0 : Fin 2))) =
            MvPolynomial.coeff (binaryPureZeroExponent m)
                ((gradientRatioLinearForm c) ^ m) * c 0 := by
        calc
          _ = MvPolynomial.coeff
              (binaryPureZeroExponent m + Finsupp.single (0 : Fin 2) 1)
              ((MvPolynomial.C (c 0) * (gradientRatioLinearForm c) ^ m) *
                MvPolynomial.X (0 : Fin 2)) := by
                  congr 1
                  ring
          _ = MvPolynomial.coeff (binaryPureZeroExponent m)
              (MvPolynomial.C (c 0) * (gradientRatioLinearForm c) ^ m) := by
                rw [MvPolynomial.coeff_mul_X]
          _ = c 0 *
              MvPolynomial.coeff (binaryPureZeroExponent m)
                ((gradientRatioLinearForm c) ^ m) := by
                rw [MvPolynomial.coeff_C_mul]
          _ = _ := by ring
      have hsecond :
          MvPolynomial.coeff
              (binaryPureZeroExponent m + Finsupp.single (0 : Fin 2) 1)
              (((gradientRatioLinearForm c) ^ m) *
                (MvPolynomial.C (c 1) * MvPolynomial.X (1 : Fin 2))) = 0 := by
        have hnot :
            (1 : Fin 2) ∉
              (binaryPureZeroExponent m +
                Finsupp.single (0 : Fin 2) 1).support := by
          simp [binaryPureZeroExponent, Finsupp.single_apply]
        calc
          _ = MvPolynomial.coeff
              (binaryPureZeroExponent m + Finsupp.single (0 : Fin 2) 1)
              ((MvPolynomial.C (c 1) * (gradientRatioLinearForm c) ^ m) *
                MvPolynomial.X (1 : Fin 2)) := by
                  congr 1
                  ring
          _ = 0 := by
                rw [MvPolynomial.coeff_mul_X']
                simp [hnot]
      rw [hfirst, hsecond, ih]
      simp [pow_succ]

/-- The adjacent U^m V coefficient of the next linear-form power. -/
theorem coeff_gradientRatioLinearForm_pow_adjacent_zero_one
    (c : Fin 2 → K)
    (m : ℕ) :
    MvPolynomial.coeff (binaryAdjacentZeroOneExponent m)
        ((gradientRatioLinearForm c) ^ (m + 1)) =
      (((m + 1 : ℕ) : K) * c 1) * (c 0) ^ m := by
  have hderiv :=
    HC4.Valuation.pderiv_gradientRatioLinearForm_pow_succ
      c (1 : Fin 2) m
  have hcoeff := congrArg
    (MvPolynomial.coeff (binaryPureZeroExponent m)) hderiv
  rw [HC4.Valuation.coeff_pderiv_commRing] at hcoeff
  simp only [binaryPureZeroExponent_one_apply, Nat.zero_add, Nat.cast_one,
    mul_one] at hcoeff
  rw [MvPolynomial.coeff_C_mul,
    coeff_gradientRatioLinearForm_pow_pure_zero] at hcoeff
  have hexp :
      binaryPureZeroExponent m + Finsupp.single (1 : Fin 2) 1 =
        binaryAdjacentZeroOneExponent m := by
    rfl
  rw [hexp] at hcoeff
  exact hcoeff

/-- If the scalar and both linear-form directions are nonzero, the pure and
adjacent channels are both genuine support monomials. -/
theorem pure_and_adjacent_mem_support_C_mul_linearPower
    {a : K} {c : Fin 2 → K} {m : ℕ}
    (ha : a ≠ 0)
    (hc0 : c 0 ≠ 0)
    (hc1 : c 1 ≠ 0) :
    binaryPureZeroExponent (m + 1) ∈
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (m + 1)).support ∧
      binaryAdjacentZeroOneExponent m ∈
        (MvPolynomial.C a * (gradientRatioLinearForm c) ^ (m + 1)).support := by
  constructor
  · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul,
      coeff_gradientRatioLinearForm_pow_pure_zero]
    exact mul_ne_zero ha (pow_ne_zero _ hc0)
  · rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul,
      coeff_gradientRatioLinearForm_pow_adjacent_zero_one]
    have hm : ((((m + 1 : ℕ) : K))) ≠ 0 := by
      exact_mod_cast (show m + 1 ≠ 0 by omega)
    exact mul_ne_zero ha
      (mul_ne_zero (mul_ne_zero hm hc1) (pow_ne_zero _ hc0))

end

end HC4.Polynomial
