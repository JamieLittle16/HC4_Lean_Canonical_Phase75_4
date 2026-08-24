import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyTransverseRankFrontier
import Mathlib.Tactic

/-!
# Logarithmic-gradient reduction of the rank-one transverse first key

Stage 4B18 leaves a single algebraic residual:

* `H` is a nonzero homogeneous ternary form of degree `m`;
* every `2 x 2` Hessian minor of `H` vanishes;
* the branch is already separated from genuine rank-two repair.

For `m >= 2`, homogeneity turns the all-minors relations into a stronger
first-order statement.  Differentiated Euler gives

    sum_l H_{i l} X_l = (m-1) H_i.

Multiplying one such identity by `H_{k j}`, another by `H_{i j}`, and using
all `2 x 2` Hessian minors yields

    H_i H_{k j} = H_k H_{i j}.

Since a nonzero positive-degree homogeneous polynomial has a nonzero first
partial derivative in characteristic zero, we may choose one gradient pivot
`r` with `H_r != 0`.  Thus every gradient component satisfies the exact
logarithmic-derivative relation

    H_r * d_j H_i = H_i * d_j H_r.

This is the precise residual needed for the final proportionality step.
No gcd/fraction-field machinery is introduced in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero positive-degree homogeneous polynomial has some nonzero first
partial derivative. -/
theorem homogeneous_exists_pderiv_ne_zero
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (m : ℕ)
    (hhom : H.IsHomogeneous m)
    (hH : H ≠ 0)
    (hm : 0 < m) :
    ∃ i : Fin n, MvPolynomial.pderiv i H ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have heuler := hhom.sum_X_mul_pderiv
  have hzero :
      (∑ i : Fin n,
          MvPolynomial.X i * MvPolynomial.pderiv i H) = 0 := by
    simp [hnone]
  rw [hzero] at heuler
  have hmK : (m : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hC :
      (MvPolynomial.C (m : K) : MvPolynomial (Fin n) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr hmK
  have hmul :
      (MvPolynomial.C (m : K) : MvPolynomial (Fin n) K) * H = 0 := by
    simpa using heuler.symm
  exact hH ((mul_eq_zero.mp hmul).resolve_left hC)

/-- For a homogeneous form of degree at least two, vanishing of every
`2 x 2` Hessian minor forces the gradient/Hessian cross relations

    H_i * H_{k j} = H_k * H_{i j}.

This is a division-free logarithmic-gradient identity. -/
theorem homogeneous_rankAtMostOne_gradient_hessian_cross
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (m : ℕ)
    (hhom : H.IsHomogeneous m)
    (hm : 2 ≤ m)
    (hall :
      ∀ i j k l : Fin n,
        HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
          HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j = 0)
    (i k j : Fin n) :
    MvPolynomial.pderiv i H * HC4.Polynomial.hessian H k j =
      MvPolynomial.pderiv k H * HC4.Polynomial.hessian H i j := by
  classical
  have hi := homogeneous_hessian_mul_X H m hhom i
  have hk := homogeneous_hessian_mul_X H m hhom k
  have hsum :
      (∑ l : Fin n,
          HC4.Polynomial.hessian H i l * MvPolynomial.X l) *
            HC4.Polynomial.hessian H k j -
        (∑ l : Fin n,
          HC4.Polynomial.hessian H k l * MvPolynomial.X l) *
            HC4.Polynomial.hessian H i j = 0 := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro l hl
    have hminor := hall i l k j
    calc
      HC4.Polynomial.hessian H i l * MvPolynomial.X l *
              HC4.Polynomial.hessian H k j -
            HC4.Polynomial.hessian H k l * MvPolynomial.X l *
              HC4.Polynomial.hessian H i j =
          MvPolynomial.X l *
            (HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j -
              HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l) := by
        ring
      _ = 0 := by
        rw [hminor]
        ring
  rw [hi, hk] at hsum
  have hpred : m - 1 ≠ 0 := by omega
  have hpredK : ((m - 1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast hpred
  have hC :
      (MvPolynomial.C (((m - 1 : ℕ) : K)) : MvPolynomial (Fin n) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr hpredK
  have hfactor :
      MvPolynomial.C (((m - 1 : ℕ) : K)) *
        (MvPolynomial.pderiv i H * HC4.Polynomial.hessian H k j -
          MvPolynomial.pderiv k H * HC4.Polynomial.hessian H i j) = 0 := by
    linear_combination hsum
  have hzero := (mul_eq_zero.mp hfactor).resolve_left hC
  exact sub_eq_zero.mp hzero

/-- The exact residual normal form after the B18 all-minors branch: choose a
nonzero gradient pivot and record that every other gradient component has the
same logarithmic derivatives as that pivot. -/
structure RankOneHomogeneousLogGradientData
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (m : ℕ) where
  pivot : Fin n
  pivot_ne_zero : MvPolynomial.pderiv pivot H ≠ 0
  cross :
    ∀ i j : Fin n,
      MvPolynomial.pderiv pivot H * HC4.Polynomial.hessian H i j =
        MvPolynomial.pderiv i H * HC4.Polynomial.hessian H pivot j

/-- Build the logarithmic-gradient residual from homogeneity and the complete
rank-at-most-one Hessian certificate. -/
theorem rankOneHomogeneousLogGradientData_of_allMinors
    {n : ℕ}
    (H : MvPolynomial (Fin n) K)
    (m : ℕ)
    (hhom : H.IsHomogeneous m)
    (hH : H ≠ 0)
    (hm : 2 ≤ m)
    (hall :
      ∀ i j k l : Fin n,
        HC4.Polynomial.hessian H i j * HC4.Polynomial.hessian H k l -
          HC4.Polynomial.hessian H i l * HC4.Polynomial.hessian H k j = 0) :
    Nonempty (RankOneHomogeneousLogGradientData H m) := by
  have hmpos : 0 < m := by omega
  rcases homogeneous_exists_pderiv_ne_zero H m hhom hH hmpos with
    ⟨r, hr⟩
  refine ⟨{
    pivot := r
    pivot_ne_zero := hr
    cross := ?_
  }⟩
  intro i j
  exact homogeneous_rankAtMostOne_gradient_hessian_cross
    H m hhom hm hall r i j

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- B18's rank-at-most-one first-key residual, strengthened by a chosen
nonzero gradient pivot and all logarithmic-gradient cross relations. -/
structure FirstKeyRankOneLogGradientResidualData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L) where
  residual : C.FirstKeyTransverseRankOneResidualData D F
  degree_ge_two : 2 ≤ D.transverseDegree
  logGradient :
    RankOneHomogeneousLogGradientData
      D.transverseSourceProfile D.transverseDegree

/-- Strengthen a B18 rank-one residual of degree at least two to the exact
logarithmic-gradient normal form. -/
theorem FirstKeyTransverseRankOneResidualData.toLogGradientResidualData
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    {D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L}
    {F : C.FirstKeyMaximalVectorLongitudinalFactorData L}
    (R : C.FirstKeyTransverseRankOneResidualData D F)
    (hm : 2 ≤ D.transverseDegree) :
    Nonempty (C.FirstKeyRankOneLogGradientResidualData D F) := by
  rcases rankOneHomogeneousLogGradientData_of_allMinors
      D.transverseSourceProfile D.transverseDegree
      D.transverseSourceProfile_homogeneous
      D.transverseSourceProfile_ne_zero hm R.allMinors with
    ⟨G⟩
  exact ⟨{
    residual := R
    degree_ge_two := hm
    logGradient := G
  }⟩

/-- **Stage 4B19 logarithmic-gradient frontier.**

The B18 residual is sharpened without introducing fractions or gcds.  Thus
we now have exactly three branches:

* transverse degree one;
* existing certified rank-two repair;
* degree at least two with a nonzero gradient pivot satisfying all
  logarithmic-gradient identities.

The third branch is the sole input needed for the final proportionality /
linear-form-power classification. -/
theorem FirstKeyCanonicalMaximalHomogeneousKernelData.degreeOne_or_rankTwoRepair_or_logGradientResidual
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    {L : C.FirstKeyLeadingTransverseKernelData}
    (D : C.FirstKeyCanonicalMaximalHomogeneousKernelData L)
    (F : C.FirstKeyMaximalVectorLongitudinalFactorData L)
    (complexity : ℕ) :
    D.transverseDegree = 1 ∨
      Nonempty (C.FirstKeyTransverseRankTwoRepairData D complexity) ∨
      Nonempty (C.FirstKeyRankOneLogGradientResidualData D F) := by
  rcases D.degreeOne_or_rankTwoRepair_or_rankOneResidual F complexity with
    hdegree | hrepair | hres
  · exact Or.inl hdegree
  · exact Or.inr (Or.inl hrepair)
  · rcases hres with ⟨R⟩
    by_cases hm1 : D.transverseDegree = 1
    · exact Or.inl hm1
    · have hmpos : 0 < D.transverseDegree := D.transverseDegree_pos
      have hm2 : 2 ≤ D.transverseDegree := by omega
      exact Or.inr (Or.inr (R.toLogGradientResidualData hm2))

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
