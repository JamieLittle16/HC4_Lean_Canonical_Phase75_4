import HC4.RationalRigidity.ChartCertificates
import Mathlib.Tactic

/-!
# Finite preimages of reduced rational functions

This file formalises the finite-chart half of the projective surjectivity
argument used in the autonomous logarithmic ODE lemma.

Let `N / D` be a reduced rational function over an algebraically closed
field.  If `y` is a scalar for which the polynomial

    N - C y * D

is nonconstant, algebraic closure supplies a root `x`.  Coprimality of `N`
and `D` then forces `D(x) != 0`, and consequently `N(x) / D(x) = y`.

For a denominator of positive degree, the coefficient at `natDegree D`
provides a convenient certificate that the difference is nonconstant.  In
particular, every scalar other than

    N.coeff (natDegree D) / D.leadingCoeff

has a genuine finite preimage.  The exceptional scalar is precisely the
value represented by the infinity chart when `natDegree N <= natDegree D`.

The final definitions package these finite values together with that one
exceptional value as the `TwoChartCover` already used by the rational-rigidity
assembly.
-/

namespace HC4.RationalRigidity

open Polynomial

noncomputable section

section Field

variable {K : Type*} [Field K]

/-- A root of `N - yD` cannot be a denominator root when `N` and `D` are
coprime. -/
theorem eval_denominator_ne_zero_of_isCoprime_sub_eval_zero
    {N D : K[X]} (hCoprime : IsCoprime N D)
    {y x : K}
    (hroot : (N - C y * D).eval x = 0) :
    D.eval x ≠ 0 := by
  intro hD
  have hN : N.eval x = 0 := by
    have h : N.eval x - y * D.eval x = 0 := by
      simpa using hroot
    rw [hD, mul_zero, sub_zero] at h
    exact h
  change ∃ A B : K[X], A * N + B * D = 1 at hCoprime
  rcases hCoprime with ⟨A, B, hBezout⟩
  have hEval := congrArg (Polynomial.eval x) hBezout
  simp [hN, hD] at hEval

/-- Once the denominator is nonzero, a root of `N - yD` is exactly a finite
preimage of `y` under the fraction `N / D`. -/
theorem div_eval_eq_of_sub_eval_zero
    {N D : K[X]} {y x : K}
    (hroot : (N - C y * D).eval x = 0)
    (hD : D.eval x ≠ 0) :
    N.eval x / D.eval x = y := by
  have hclear : N.eval x - y * D.eval x = 0 := by
    simpa using hroot
  apply (div_eq_iff hD).2
  exact sub_eq_zero.mp hclear

end Field

section AlgebraicallyClosedField

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A nonconstant reduced fibre polynomial has a genuine finite preimage. -/
theorem exists_finite_preimage_of_isCoprime
    {N D : K[X]} (hCoprime : IsCoprime N D)
    {y : K}
    (hnonconstant : (N - C y * D).natDegree ≠ 0) :
    ∃ x : K, D.eval x ≠ 0 ∧ N.eval x / D.eval x = y := by
  let P : K[X] := N - C y * D
  have hdegree : P.degree ≠ 0 := by
    intro hdegree
    have hconst : P = C (P.coeff 0) :=
      Polynomial.eq_C_of_degree_eq_zero hdegree
    have hnat : P.natDegree = 0 := by
      rw [hconst]
      simp
    exact hnonconstant hnat
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P hdegree
  have hroot : (N - C y * D).eval x = 0 := by
    exact hx
  have hD : D.eval x ≠ 0 :=
    eval_denominator_ne_zero_of_isCoprime_sub_eval_zero hCoprime hroot
  exact ⟨x, hD, div_eval_eq_of_sub_eval_zero hroot hD⟩

/-- A nonzero coefficient in positive degree certifies that a polynomial is
nonconstant. -/
theorem natDegree_ne_zero_of_coeff_ne_zero
    {P : K[X]} {d : ℕ}
    (hd : 0 < d) (hcoeff : P.coeff d ≠ 0) :
    P.natDegree ≠ 0 := by
  intro hnat
  have hconst : P = C (P.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hnat
  have hz : P.coeff d = 0 := by
    rw [hconst, Polynomial.coeff_C]
    simp [Nat.ne_of_gt hd]
  exact hcoeff hz

/-- If the coefficient at the denominator degree does not cancel, then the
reduced fraction has a finite preimage of `y`. -/
theorem exists_finite_preimage_of_isCoprime_of_topCoeff_ne
    {N D : K[X]} (hCoprime : IsCoprime N D)
    {y : K}
    (hDdegree : 0 < D.natDegree)
    (htop : N.coeff D.natDegree ≠ y * D.leadingCoeff) :
    ∃ x : K, D.eval x ≠ 0 ∧ N.eval x / D.eval x = y := by
  have hcoeff :
      (N - C y * D).coeff D.natDegree ≠ 0 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    change N.coeff D.natDegree - y * D.leadingCoeff ≠ 0
    exact sub_ne_zero.mpr htop
  have hnonconstant : (N - C y * D).natDegree ≠ 0 :=
    natDegree_ne_zero_of_coeff_ne_zero hDdegree hcoeff
  exact exists_finite_preimage_of_isCoprime hCoprime hnonconstant

/-- The unique scalar potentially missed by the finite chart of a reduced
fraction whose denominator has positive degree. -/
def rationalInfinityValue
    (N D : K[X]) : K :=
  N.coeff D.natDegree / D.leadingCoeff

/-- Every scalar other than `rationalInfinityValue N D` has a genuine finite
preimage under a reduced fraction with positive-degree nonzero denominator. -/
theorem exists_finite_preimage_away_from_rationalInfinityValue
    {N D : K[X]} (hCoprime : IsCoprime N D)
    (hD : D ≠ 0) (hDdegree : 0 < D.natDegree)
    {y : K}
    (hy : y ≠ rationalInfinityValue N D) :
    ∃ x : K, D.eval x ≠ 0 ∧ N.eval x / D.eval x = y := by
  have hlc : D.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hD
  have htop : N.coeff D.natDegree ≠ y * D.leadingCoeff := by
    intro h
    apply hy
    unfold rationalInfinityValue
    apply (eq_div_iff hlc).2
    exact h.symm
  exact exists_finite_preimage_of_isCoprime_of_topCoeff_ne
    hCoprime hDdegree htop

/-- Finite target values for the reduced fraction. -/
def FiniteTargetChart
    (N D : K[X]) : Type _ :=
  {y : K // y ≠ rationalInfinityValue N D}

/-- The finite chart simply remembers its represented scalar. -/
def finiteTargetValue
    (N D : K[X]) : FiniteTargetChart N D → K :=
  fun y => y.1

/-- The one-point infinity chart represents the exceptional scalar. -/
def infinityTargetValue
    (N D : K[X]) : PUnit → K :=
  fun _ => rationalInfinityValue N D

/-- The finite values together with the single infinity value cover every
scalar.  This is the target-side `TwoChartCover` needed by the existing
rational-rigidity assembly. -/
theorem finite_infinity_target_cover
    (N D : K[X]) :
    TwoChartCover (finiteTargetValue N D) (infinityTargetValue N D) := by
  intro y
  by_cases hy : y = rationalInfinityValue N D
  · right
    refine ⟨PUnit.unit, ?_⟩
    simpa [infinityTargetValue] using hy.symm
  · left
    exact ⟨⟨y, hy⟩, rfl⟩

end AlgebraicallyClosedField

end

end HC4.RationalRigidity
