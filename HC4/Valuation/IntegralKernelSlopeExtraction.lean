import HC4.Valuation.ExactKernelDefectDrop
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Maximal integral kernel-slope extraction

The preceding valuation files prove everything that happens *after* a
positive integral kernel slope has been chosen.

This file chooses that slope from the actual polynomial coefficients.

Fix an active source coordinate `kernel`.  A natural number `q` is
admissible when every source monomial of kernel degree `r` has coefficient
divisible by

    tau^(q*r).

This is exactly `HasIntegralKernelCoefficientDivisibility`.

Because the source polynomial has finite support, and because the kernel
coordinate is assumed active, every admissible slope is bounded by the
parameter degree of one fixed active coefficient.  Thus the admissible
slopes form a nonempty finite set: `q = 0` is always admissible.

We define the maximal integral kernel slope to be the maximum of that
finite set and prove:

* it satisfies the coefficient divisibility condition;
* every other admissible integral slope is at most it;
* it is either zero or strictly positive;
* it is zero exactly when no positive admissible integral slope exists.

The positive branch then plugs directly into Phase 93.57, producing the
exact Hessian defect drop and strict global restart.

No abstract restart/exposure hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Active kernel coordinate -/

/-- The chosen kernel source coordinate actually occurs in at least one
source monomial of the family. -/
def IsActiveKernelCoordinate
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K)) : Prop :=
  ∃ d ∈ P.support, 0 < d kernel

/-- A chosen active source exponent. -/
noncomputable def activeKernelExponent
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    Fin 4 →₀ ℕ :=
  Classical.choose hactive

theorem activeKernelExponent_mem
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    activeKernelExponent kernel P hactive ∈ P.support := by
  exact (Classical.choose_spec hactive).1

theorem activeKernelExponent_pos
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    0 < (activeKernelExponent kernel P hactive) kernel := by
  exact (Classical.choose_spec hactive).2

/-- A concrete finite bound for every admissible integral kernel slope:
the `tau`-degree of one fixed active coefficient. -/
noncomputable def integralKernelSlopeBound
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    ℕ :=
  (MvPolynomial.coeff
    (activeKernelExponent kernel P hactive) P).natDegree

/-- Every admissible integral slope is bounded by
`integralKernelSlopeBound`. -/
theorem admissibleIntegralKernelSlope_le_bound
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (q : ℕ)
    (hq :
      HasIntegralKernelCoefficientDivisibility
        kernel q P) :
    q ≤ integralKernelSlopeBound kernel P hactive := by
  let d :=
    activeKernelExponent kernel P hactive
  have hd : d ∈ P.support := by
    exact activeKernelExponent_mem kernel P hactive
  have hdpos : 0 < d kernel := by
    exact activeKernelExponent_pos kernel P hactive
  have hcne :
      MvPolynomial.coeff d P ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hdvd :=
    hq d hd
  rcases hdvd with ⟨R, hR⟩
  have hRne : R ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hR
    exact hcne hR
  have hpowne :
      kernelCoefficientTauPower
          (K := K) kernel q d ≠ 0 := by
    unfold kernelCoefficientTauPower
    exact
      pow_ne_zero
        (q * d kernel)
        Polynomial.X_ne_zero
  have hdeg :
      (MvPolynomial.coeff d P).natDegree =
        (kernelCoefficientTauPower
            (K := K) kernel q d).natDegree +
          R.natDegree := by
    rw [hR]
    exact
      Polynomial.natDegree_mul
        hpowne hRne
  have hpowdeg :
      (kernelCoefficientTauPower
          (K := K) kernel q d).natDegree =
        q * d kernel := by
    simp [kernelCoefficientTauPower]
  have hqd :
      q * d kernel ≤
        (MvPolynomial.coeff d P).natDegree := by
    rw [hdeg, hpowdeg]
    omega
  have hq_qd :
      q ≤ q * d kernel := by
    have hone : 1 ≤ d kernel :=
      hdpos
    calc
      q = q * 1 := by simp
      _ ≤ q * d kernel :=
        Nat.mul_le_mul_left q hone
  have hqdeg :
      q ≤ (MvPolynomial.coeff d P).natDegree :=
    le_trans hq_qd hqd
  simpa [integralKernelSlopeBound, d] using hqdeg

/-! ## Finite admissible slope set -/

/-- Finite set of all admissible integral slopes.

The range bound is complete by
`admissibleIntegralKernelSlope_le_bound`. -/
noncomputable def integralKernelSlopeCandidates
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    Finset ℕ := by
  classical
  exact
    (Finset.range
      (integralKernelSlopeBound kernel P hactive + 1)).filter
        (fun q =>
          HasIntegralKernelCoefficientDivisibility
            kernel q P)

/-- Slope zero is always admissible. -/
theorem zero_mem_integralKernelSlopeCandidates
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    0 ∈ integralKernelSlopeCandidates
      kernel P hactive := by
  classical
  simp [integralKernelSlopeCandidates,
    HasIntegralKernelCoefficientDivisibility,
    kernelCoefficientTauPower]

/-- The candidate set is nonempty. -/
theorem integralKernelSlopeCandidates_nonempty
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    (integralKernelSlopeCandidates
      kernel P hactive).Nonempty := by
  exact
    ⟨0,
      zero_mem_integralKernelSlopeCandidates
        kernel P hactive⟩

/-- **Maximal integral Newton kernel slope.** -/
noncomputable def maximalIntegralKernelSlope
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    ℕ :=
  (integralKernelSlopeCandidates
    kernel P hactive).max'
      (integralKernelSlopeCandidates_nonempty
        kernel P hactive)

/-- The selected maximal slope is itself one of the admissible candidates. -/
theorem maximalIntegralKernelSlope_mem
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    maximalIntegralKernelSlope kernel P hactive ∈
      integralKernelSlopeCandidates
        kernel P hactive := by
  unfold maximalIntegralKernelSlope
  exact
    Finset.max'_mem
      (integralKernelSlopeCandidates
        kernel P hactive)
      (integralKernelSlopeCandidates_nonempty
        kernel P hactive)

/-- Therefore the selected slope satisfies the exact coefficient
divisibility required by the concrete blow-up constructor. -/
theorem maximalIntegralKernelSlope_divisibility
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    HasIntegralKernelCoefficientDivisibility
      kernel
      (maximalIntegralKernelSlope kernel P hactive)
      P := by
  classical
  have hmem :=
    maximalIntegralKernelSlope_mem
      kernel P hactive
  have hmem' :
      maximalIntegralKernelSlope kernel P hactive <
          integralKernelSlopeBound kernel P hactive + 1 ∧
        HasIntegralKernelCoefficientDivisibility
          kernel
          (maximalIntegralKernelSlope kernel P hactive)
          P := by
    simpa [integralKernelSlopeCandidates] using hmem
  exact hmem'.2

/-- Every admissible integral kernel slope lies below the selected one. -/
theorem admissibleIntegralKernelSlope_le_maximal
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (q : ℕ)
    (hq :
      HasIntegralKernelCoefficientDivisibility
        kernel q P) :
    q ≤ maximalIntegralKernelSlope
      kernel P hactive := by
  have hbound :
      q ≤ integralKernelSlopeBound
        kernel P hactive :=
    admissibleIntegralKernelSlope_le_bound
      kernel P hactive q hq
  have hmem :
      q ∈ integralKernelSlopeCandidates
        kernel P hactive := by
    classical
    simp [integralKernelSlopeCandidates,
      Nat.lt_succ_iff.mpr hbound, hq]
  unfold maximalIntegralKernelSlope
  exact
    Finset.le_max'
      (integralKernelSlopeCandidates
        kernel P hactive)
      q hmem

/-! ## Exact zero/positive dichotomy -/

/-- If the maximal slope is zero, there is no positive admissible integral
kernel slope. -/
theorem no_positive_admissible_of_maximalIntegralKernelSlope_eq_zero
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (hzero :
      maximalIntegralKernelSlope
        kernel P hactive = 0) :
    ¬ ∃ q : ℕ,
      0 < q ∧
      HasIntegralKernelCoefficientDivisibility
        kernel q P := by
  rintro ⟨q, hqpos, hqdiv⟩
  have hle :=
    admissibleIntegralKernelSlope_le_maximal
      kernel P hactive q hqdiv
  rw [hzero] at hle
  omega

/-- Conversely, if there is no positive admissible integral slope, the
selected maximal slope is zero. -/
theorem maximalIntegralKernelSlope_eq_zero_of_no_positive_admissible
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (hnone :
      ¬ ∃ q : ℕ,
        0 < q ∧
        HasIntegralKernelCoefficientDivisibility
          kernel q P) :
    maximalIntegralKernelSlope
        kernel P hactive = 0 := by
  have hdiv :=
    maximalIntegralKernelSlope_divisibility
      kernel P hactive
  rcases Nat.eq_zero_or_pos
      (maximalIntegralKernelSlope
        kernel P hactive) with
    hzero | hpos
  · exact hzero
  · exfalso
    exact
      hnone
        ⟨maximalIntegralKernelSlope
            kernel P hactive,
          hpos, hdiv⟩

/-- Characterisation of the zero-slope branch. -/
theorem maximalIntegralKernelSlope_eq_zero_iff
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    maximalIntegralKernelSlope
        kernel P hactive = 0 ↔
      ¬ ∃ q : ℕ,
        0 < q ∧
        HasIntegralKernelCoefficientDivisibility
          kernel q P := by
  constructor
  · exact
      no_positive_admissible_of_maximalIntegralKernelSlope_eq_zero
        kernel P hactive
  · exact
      maximalIntegralKernelSlope_eq_zero_of_no_positive_admissible
        kernel P hactive

/-- **Concrete Newton-slope dichotomy.**

Either no positive integral kernel blow-up exists, or the selected maximal
positive slope comes equipped with the exact divisibility data consumed by
the green blow-up machinery. -/
theorem maximalIntegralKernelSlope_zero_or_positive
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P) :
    (maximalIntegralKernelSlope
          kernel P hactive = 0 ∧
        ¬ ∃ q : ℕ,
          0 < q ∧
          HasIntegralKernelCoefficientDivisibility
            kernel q P) ∨
      (0 <
          maximalIntegralKernelSlope
            kernel P hactive ∧
        HasIntegralKernelCoefficientDivisibility
          kernel
          (maximalIntegralKernelSlope
            kernel P hactive)
          P) := by
  rcases Nat.eq_zero_or_pos
      (maximalIntegralKernelSlope
        kernel P hactive) with
    hzero | hpos
  · left
    exact
      ⟨hzero,
        no_positive_admissible_of_maximalIntegralKernelSlope_eq_zero
          kernel P hactive hzero⟩
  · right
    exact
      ⟨hpos,
        maximalIntegralKernelSlope_divisibility
          kernel P hactive⟩

/-! ## Positive maximal slope plugs directly into global restart -/

/-- **Maximal-slope exact defect and strict restart.**

Once the geometric marked-section normalisation supplies distinct special
points, the positive maximal integral slope selected above invokes the
complete Phase 93.57 restart theorem with no separate slope or divisibility
choice. -/
theorem maximalIntegralKernelSlope_exactDefect_and_strictRestart
    {s : GlobalRestartState}
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    {Delta : ℕ}
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (hspecialDistinct :
      polynomialSectionSpecialPoint
          (kernelBlowupSection
            kernel
            (maximalIntegralKernelSlope
              kernel P hactive)
            a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection
            kernel
            (maximalIntegralKernelSlope
              kernel P hactive)
            b))
    (hslope :
      0 <
        maximalIntegralKernelSlope
          kernel P hactive)
    (hs :
      s.defect = Delta)
    (newRepair : RepairState) :
    let q :=
      maximalIntegralKernelSlope
        kernel P hactive
    let t : GlobalRestartState :=
      { defect := Delta - 2 * q
        repair := newRepair }
    HasPolynomialFamilyHessianDefect
        (K := K)
        (integralKernelBlowupFamily
          kernel q P
          (maximalIntegralKernelSlope_divisibility
            kernel P hactive))
        (Delta - 2 * q) ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily
            kernel q P
            (maximalIntegralKernelSlope_divisibility
              kernel P hactive)))
        (polynomialSectionSpecialPoint
          (kernelBlowupSection kernel q a))
        (polynomialSectionSpecialPoint
          (kernelBlowupSection kernel q b)) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  dsimp
  have hout :=
    integralKernelBlowup_exactDefect_and_strictRestart
      (s := s)
      (t :=
        { defect :=
            Delta -
              2 *
                maximalIntegralKernelSlope
                  kernel P hactive
          repair := newRepair })
      kernel hslope P
      (maximalIntegralKernelSlope_divisibility
        kernel P hactive)
      hdef a b hcoll
      hspecialDistinct
      hs
      rfl
  exact
    ⟨hout.1,
      hout.2.2.1,
      hout.2.2.2.1,
      hout.2.2.2.2⟩

/-- In the zero-slope branch the explicit blow-up is literally the identity,
so no spurious global restart is performed. -/
theorem maximalIntegralKernelSlope_zero_identity
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hactive : IsActiveKernelCoordinate kernel P)
    (hzero :
      maximalIntegralKernelSlope
        kernel P hactive = 0)
    (a : Fin 4 → Polynomial K) :
    integralKernelBlowupFamily
        kernel
        (maximalIntegralKernelSlope kernel P hactive)
        P
        (maximalIntegralKernelSlope_divisibility
          kernel P hactive) = P ∧
      kernelBlowupSection
        kernel
        (maximalIntegralKernelSlope kernel P hactive)
        a = a := by
  have hdiv0 :
      HasIntegralKernelCoefficientDivisibility
        kernel 0 P := by
    intro d hd
    simp [kernelCoefficientTauPower]
  simpa only [hzero] using
    (integralKernelBlowup_zero_is_identity
      kernel P hdiv0 a)

end

end HC4.Valuation
