import HC4.Valuation.PolynomialFamilyKernelRestart
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Integral kernel blow-up by coefficient division

This file formalises the integrality half of the kernel blow-up lemma.

Let `P` be a multivariate polynomial family with coefficients in `K[τ]`,
and let `T` be the chosen kernel source coordinate.  For a positive integral
slope `q`, the formal kernel blow-up is

    P̃(X,T) = P(X, τ^{-q} T).

This expression is not formed using negative powers in Lean.  Instead, for
each source monomial exponent `d`, one requires the coefficient of `X^d` in
`P` to be divisible by

    τ^(q * d(T)).

Lean then chooses the quotient coefficient for every monomial in the finite
support and reconstructs the transformed polynomial `P̃` explicitly as a
finite sum of monomials.

The resulting theorem proves coefficientwise

    coeff_d(P)
      = τ^(q * d(T)) * coeff_d(P̃)

for every exponent `d`, including exponents outside the original support.
This is the exact polynomial-ring meaning of the statement

    P̃(X,T) = P(X, τ^{-q} T) ∈ K[τ][X,T].

The second section defines the corresponding integral transformation of a
moving marked section: multiply its kernel coordinate by `τ^q`.
-/

namespace HC4.Valuation

noncomputable section

open scoped BigOperators

variable {σ K : Type*} [Field K] [DecidableEq σ]

/-- The power of the Rees parameter that must divide the coefficient of a
source monomial `d` when the source coordinate `kernel` is blown up at
integral slope `slope`. -/
def kernelCoefficientTauPower
    (kernel : σ)
    (slope : ℕ)
    (d : σ →₀ ℕ) :
    Polynomial K :=
  Polynomial.X ^ (slope * d kernel)

/-- Coefficientwise integrality condition for the kernel blow-up.

For each monomial occurring in `P`, the coefficient is divisible by the
power of `τ` forced by its degree in the chosen kernel coordinate. -/
def HasIntegralKernelCoefficientDivisibility
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K)) : Prop :=
  ∀ d ∈ P.support,
    kernelCoefficientTauPower kernel slope d ∣
      MvPolynomial.coeff d P

/-- Chosen quotient coefficient for one source monomial.

Outside the support of `P` we set the quotient to zero. -/
noncomputable def kernelCoefficientQuotient
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (d : σ →₀ ℕ) :
    Polynomial K :=
  if hd : d ∈ P.support then
    Classical.choose (hdiv d hd)
  else
    0

/-- On the actual support, the chosen quotient has the required exact
factorisation. -/
theorem kernelCoefficientQuotient_spec_of_mem
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    {d : σ →₀ ℕ}
    (hd : d ∈ P.support) :
    MvPolynomial.coeff d P =
      kernelCoefficientTauPower kernel slope d *
        kernelCoefficientQuotient
          kernel slope P hdiv d := by
  unfold kernelCoefficientQuotient
  rw [dif_pos hd]
  exact Classical.choose_spec (hdiv d hd)

/-- Explicit integral kernel blow-up polynomial, reconstructed from the
chosen quotient coefficients over the finite support of `P`. -/
noncomputable def integralKernelBlowupFamily
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P) :
    MvPolynomial σ (Polynomial K) :=
  ∑ d ∈ P.support,
    MvPolynomial.monomial d
      (kernelCoefficientQuotient
        kernel slope P hdiv d)

/-- Exact coefficient formula for the reconstructed blow-up polynomial. -/
theorem coeff_integralKernelBlowupFamily
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (d : σ →₀ ℕ) :
    MvPolynomial.coeff d
        (integralKernelBlowupFamily
          kernel slope P hdiv) =
      if d ∈ P.support then
        kernelCoefficientQuotient
          kernel slope P hdiv d
      else
        0 := by
  classical
  unfold integralKernelBlowupFamily
  by_cases hd : d ∈ P.support
  · simp [MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, hd]
  · simp [MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, hd]

/-- The blow-up introduces no new source monomials. -/
theorem support_integralKernelBlowupFamily_subset
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P) :
    (integralKernelBlowupFamily
      kernel slope P hdiv).support ⊆
        P.support := by
  intro d hd
  by_contra hnot
  have hzero :
      MvPolynomial.coeff d
          (integralKernelBlowupFamily
            kernel slope P hdiv) = 0 := by
    rw [coeff_integralKernelBlowupFamily]
    simp [hnot]
  exact
    (MvPolynomial.mem_support_iff.mp hd) hzero

/-- Exact coefficientwise meaning of an integral kernel blow-up. -/
def IsIntegralKernelBlowup
    (kernel : σ)
    (slope : ℕ)
    (P Ptilde : MvPolynomial σ (Polynomial K)) : Prop :=
  ∀ d : σ →₀ ℕ,
    MvPolynomial.coeff d P =
      kernelCoefficientTauPower kernel slope d *
        MvPolynomial.coeff d Ptilde

/-- **Integral kernel blow-up constructor.**

The coefficient divisibility condition is sufficient to construct an
honest polynomial family over `K[τ]` satisfying the exact coefficientwise
rescaling identity. -/
theorem integralKernelBlowupFamily_isIntegralKernelBlowup
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P) :
    IsIntegralKernelBlowup
      kernel slope P
      (integralKernelBlowupFamily
        kernel slope P hdiv) := by
  intro d
  by_cases hd : d ∈ P.support
  · rw [coeff_integralKernelBlowupFamily]
    simp only [if_pos hd]
    exact
      kernelCoefficientQuotient_spec_of_mem
        kernel slope P hdiv hd
  · have hP :
        MvPolynomial.coeff d P = 0 :=
      (MvPolynomial.notMem_support_iff.mp hd)
    rw [hP, coeff_integralKernelBlowupFamily]
    simp [hd]

/-- Coefficients independent of the blown-up source coordinate are
unchanged. -/
theorem integralKernelBlowupFamily_coeff_of_kernelDegree_zero
    (kernel : σ)
    (slope : ℕ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (d : σ →₀ ℕ)
    (hdegree : d kernel = 0) :
    MvPolynomial.coeff d P =
      MvPolynomial.coeff d
        (integralKernelBlowupFamily
          kernel slope P hdiv) := by
  have hspec :=
    integralKernelBlowupFamily_isIntegralKernelBlowup
      kernel slope P hdiv d
  simp [kernelCoefficientTauPower, hdegree] at hspec
  exact hspec

/-- At slope zero, the coefficientwise blow-up identity is trivial. -/
theorem integralKernelBlowupFamily_coeff_slope_zero
    (kernel : σ)
    (P : MvPolynomial σ (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel 0 P)
    (d : σ →₀ ℕ) :
    MvPolynomial.coeff d P =
      MvPolynomial.coeff d
        (integralKernelBlowupFamily
          kernel 0 P hdiv) := by
  have hspec :=
    integralKernelBlowupFamily_isIntegralKernelBlowup
      kernel 0 P hdiv d
  simpa [kernelCoefficientTauPower] using hspec

/-! ## Integral transformation of moving sections -/

/-- Moving marked section under the kernel blow-up.

The blown-up source coordinate is multiplied by `τ^slope`; all other
coordinates are unchanged.  This is polynomial for every natural slope. -/
def kernelBlowupSection
    (kernel : σ)
    (slope : ℕ)
    (a : σ → Polynomial K) :
    σ → Polynomial K :=
  fun i =>
    if i = kernel then
      Polynomial.X ^ slope * a i
    else
      a i

/-- Coordinates away from the kernel direction are unchanged. -/
theorem kernelBlowupSection_apply_of_ne
    (kernel : σ)
    (slope : ℕ)
    (a : σ → Polynomial K)
    {i : σ}
    (hi : i ≠ kernel) :
    kernelBlowupSection kernel slope a i =
      a i := by
  simp [kernelBlowupSection, hi]

/-- The kernel coordinate is multiplied by the positive Rees power. -/
theorem kernelBlowupSection_apply_kernel
    (kernel : σ)
    (slope : ℕ)
    (a : σ → Polynomial K) :
    kernelBlowupSection kernel slope a kernel =
      Polynomial.X ^ slope * a kernel := by
  simp [kernelBlowupSection]

/-- At zero slope the section is unchanged. -/
theorem kernelBlowupSection_zero
    (kernel : σ)
    (a : σ → Polynomial K) :
    kernelBlowupSection kernel 0 a = a := by
  funext i
  by_cases hi : i = kernel
  · subst i
    simp [kernelBlowupSection]
  · simp [kernelBlowupSection, hi]

/-- For a positive kernel slope, the special-fibre kernel coordinate of the
blown-up section is zero. -/
theorem polynomialSectionSpecialPoint_kernelBlowupSection_kernel
    (kernel : σ)
    {slope : ℕ}
    (hslope : 0 < slope)
    (a : σ → Polynomial K) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection kernel slope a)
        kernel = 0 := by
  unfold polynomialSectionSpecialPoint
  rw [kernelBlowupSection_apply_kernel]
  rw [map_mul]
  have hX :
      Polynomial.constantCoeff
          (Polynomial.X ^ slope : Polynomial K) = 0 := by
    have hslope0 : slope ≠ 0 :=
      Nat.ne_of_gt hslope
    rw [map_pow]
    simp [hslope0]
  rw [hX]
  simp

/-- Away from the kernel coordinate, specialisation of the moving section
is unchanged. -/
theorem polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
    (kernel : σ)
    (slope : ℕ)
    (a : σ → Polynomial K)
    {i : σ}
    (hi : i ≠ kernel) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection kernel slope a)
        i =
      polynomialSectionSpecialPoint a i := by
  unfold polynomialSectionSpecialPoint
  rw [kernelBlowupSection_apply_of_ne
    kernel slope a hi]


/-! ## Exact evaluation covariance in four source variables

The coefficient identity alone already implies the genuine substitution
identity at the level of evaluation:

    Ptilde(kernelBlowupSection a) = P(a).

We prove it directly from `MvPolynomial.eval_eq'`, which expands evaluation
as the coefficient sum over all four source coordinates.
-/

/-- Product identity for one source monomial in four variables.

Multiplying the kernel coordinate of the moving section by `τ^slope`
contributes exactly the factor `τ^(slope * d(kernel))`. -/
theorem fin4_kernelBlowupSection_monomialProduct
    (kernel : Fin 4)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (d : Fin 4 →₀ ℕ) :
    (∏ i : Fin 4,
        kernelBlowupSection kernel slope a i ^ d i) =
      kernelCoefficientTauPower kernel slope d *
        ∏ i : Fin 4, a i ^ d i := by
  fin_cases kernel <;>
    simp [kernelBlowupSection,
      kernelCoefficientTauPower,
      Fin.prod_univ_four, mul_pow, pow_mul] <;>
    ring

/-- **Exact evaluation covariance of the integral kernel blow-up.**

For the explicitly reconstructed integral blow-up family `Ptilde`,
evaluation at the blown-up moving section agrees exactly with evaluation of
the original family at the original section.

This is the honest polynomial-ring version of

    Ptilde(X, τ^q T) = P(X,T).
-/
theorem eval_integralKernelBlowupFamily_kernelBlowupSection
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        (integralKernelBlowupFamily
          kernel slope P hdiv) =
      MvPolynomial.eval a P := by
  classical
  unfold integralKernelBlowupFamily
  simp only [MvPolynomial.eval_sum,
    MvPolynomial.eval_monomial]
  rw [MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro d hd
  rw [kernelCoefficientQuotient_spec_of_mem
    kernel slope P hdiv hd]
  rw [Finsupp.prod_fintype
    d
    (fun n e =>
      kernelBlowupSection kernel slope a n ^ e)
    (by
      intro i
      simp)]
  rw [fin4_kernelBlowupSection_monomialProduct]
  ring

/-- Two source sections with equal original evaluations retain equal
evaluations after the integral blow-up. -/
theorem eval_integralKernelBlowupFamily_eq_of_eq
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (h :
      MvPolynomial.eval a P =
        MvPolynomial.eval b P) :
    MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        (integralKernelBlowupFamily
          kernel slope P hdiv) =
      MvPolynomial.eval
        (kernelBlowupSection kernel slope b)
        (integralKernelBlowupFamily
          kernel slope P hdiv) := by
  rw [eval_integralKernelBlowupFamily_kernelBlowupSection]
  rw [eval_integralKernelBlowupFamily_kernelBlowupSection]
  exact h


/-! ## Partial-derivative covariance

We now differentiate the exact integral blow-up identity in the source
variables.

For a non-kernel source direction `i`, the Rees power attached to a
monomial is unchanged after lowering its `i`-exponent by one.

For the kernel direction itself, lowering the kernel exponent by one
removes exactly one factor `τ^slope`.  Consequently

    τ^slope * (∂_kernel Ptilde)(blowup(a))
      = (∂_kernel P)(a).

These two identities are precisely what is needed to transport an exact
family-gradient collision through the concrete integral kernel blow-up.
-/

/-- Lowering a non-kernel exponent does not change its kernel Rees power. -/
theorem kernelCoefficientTauPower_sub_single_of_ne
    (kernel i : Fin 4)
    (hi : i ≠ kernel)
    (slope : ℕ)
    (d : Fin 4 →₀ ℕ) :
    kernelCoefficientTauPower (K := K)
        kernel slope
        (d - (Finsupp.single i 1 : Fin 4 →₀ ℕ)) =
      kernelCoefficientTauPower (K := K)
        kernel slope d := by
  unfold kernelCoefficientTauPower
  have hdegree :
      (d - (Finsupp.single i 1 : Fin 4 →₀ ℕ)) kernel =
        d kernel := by
    simp [hi, Ne.symm hi]
  rw [hdegree]

/-- Product covariance after differentiating in a non-kernel coordinate. -/
theorem fin4_kernelBlowupSection_derivativeProduct_of_ne
    (kernel i : Fin 4)
    (hi : i ≠ kernel)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (d : Fin 4 →₀ ℕ) :
    (∏ j : Fin 4,
        kernelBlowupSection kernel slope a j ^
          ((d - (Finsupp.single i 1 : Fin 4 →₀ ℕ)) j)) =
      kernelCoefficientTauPower kernel slope d *
        ∏ j : Fin 4,
          a j ^ ((d - (Finsupp.single i 1 : Fin 4 →₀ ℕ)) j) := by
  have h :=
    fin4_kernelBlowupSection_monomialProduct
      kernel slope a
      (d - (Finsupp.single i 1 : Fin 4 →₀ ℕ))
  rw [kernelCoefficientTauPower_sub_single_of_ne
    kernel i hi slope d] at h
  exact h

/-- Product covariance after differentiating in the kernel coordinate.

The missing kernel exponent is restored by the single external factor
`τ^slope`. -/
theorem fin4_kernelBlowupSection_derivativeProduct_kernel
    (kernel : Fin 4)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (d : Fin 4 →₀ ℕ)
    (hd : d kernel ≠ 0) :
    Polynomial.X ^ slope *
        (∏ j : Fin 4,
          kernelBlowupSection kernel slope a j ^
            ((d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ)) j)) =
      kernelCoefficientTauPower kernel slope d *
        ∏ j : Fin 4,
          a j ^ ((d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ)) j) := by
  have h :=
    fin4_kernelBlowupSection_monomialProduct
      kernel slope a
      (d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ))
  rw [h]
  unfold kernelCoefficientTauPower
  have hsub :
      (d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ)) kernel =
        d kernel - 1 := by
    simp
  rw [hsub]
  have hpos : 0 < d kernel :=
    Nat.pos_of_ne_zero hd
  have hone : 1 ≤ d kernel :=
    hpos
  have hrecover :
      d kernel - 1 + 1 = d kernel :=
    Nat.sub_add_cancel hone
  have hexp :
      slope + slope * (d kernel - 1) =
        slope * d kernel := by
    calc
      slope + slope * (d kernel - 1) =
          slope * (d kernel - 1) + slope := by
            rw [Nat.add_comm]
      _ = slope * ((d kernel - 1) + 1) := by
            rw [Nat.mul_add]
            simp
      _ = slope * d kernel := by
            rw [hrecover]
  rw [← mul_assoc, ← pow_add, hexp]

/-- Monomial-level non-kernel partial-derivative covariance. -/
theorem eval_pderiv_monomial_kernelBlowupSection_of_ne
    (kernel i : Fin 4)
    (hi : i ≠ kernel)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (d : Fin 4 →₀ ℕ)
    (c : Polynomial K) :
    MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        (MvPolynomial.pderiv i
          (MvPolynomial.monomial d c)) =
      MvPolynomial.eval a
        (MvPolynomial.pderiv i
          (MvPolynomial.monomial d
            (kernelCoefficientTauPower
              kernel slope d * c))) := by
  rw [MvPolynomial.pderiv_monomial,
      MvPolynomial.pderiv_monomial,
      MvPolynomial.eval_monomial,
      MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype
    (d - (Finsupp.single i 1 : Fin 4 →₀ ℕ))
    (fun n e =>
      kernelBlowupSection kernel slope a n ^ e)
    (by
      intro j
      simp)]
  rw [Finsupp.prod_fintype
    (d - (Finsupp.single i 1 : Fin 4 →₀ ℕ))
    (fun n e => a n ^ e)
    (by
      intro j
      simp)]
  rw [fin4_kernelBlowupSection_derivativeProduct_of_ne
    kernel i hi slope a d]
  ring

/-- Monomial-level kernel partial-derivative covariance. -/
theorem eval_pderiv_monomial_kernelBlowupSection_kernel
    (kernel : Fin 4)
    (slope : ℕ)
    (a : Fin 4 → Polynomial K)
    (d : Fin 4 →₀ ℕ)
    (c : Polynomial K) :
    Polynomial.X ^ slope *
      MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        (MvPolynomial.pderiv kernel
          (MvPolynomial.monomial d c)) =
      MvPolynomial.eval a
        (MvPolynomial.pderiv kernel
          (MvPolynomial.monomial d
            (kernelCoefficientTauPower
              kernel slope d * c))) := by
  by_cases hd : d kernel = 0
  · simp [MvPolynomial.pderiv_monomial, hd]
  · rw [MvPolynomial.pderiv_monomial,
        MvPolynomial.pderiv_monomial,
        MvPolynomial.eval_monomial,
        MvPolynomial.eval_monomial]
    rw [Finsupp.prod_fintype
      (d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ))
      (fun n e =>
        kernelBlowupSection kernel slope a n ^ e)
      (by
        intro j
        simp)]
    rw [Finsupp.prod_fintype
      (d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ))
      (fun n e => a n ^ e)
      (by
        intro j
        simp)]
    have hprod :=
      fin4_kernelBlowupSection_derivativeProduct_kernel
        kernel slope a d hd
    calc
      Polynomial.X ^ slope *
          (c * (d kernel : Polynomial K) *
            ∏ i : Fin 4,
              kernelBlowupSection kernel slope a i ^
                ((d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ)) i)) =
        c * (d kernel : Polynomial K) *
          (Polynomial.X ^ slope *
            ∏ i : Fin 4,
              kernelBlowupSection kernel slope a i ^
                ((d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ)) i)) := by
          ring
      _ =
        c * (d kernel : Polynomial K) *
          (kernelCoefficientTauPower kernel slope d *
            ∏ i : Fin 4,
              a i ^
                ((d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ)) i)) := by
          rw [hprod]
      _ =
        kernelCoefficientTauPower kernel slope d *
          c * (d kernel : Polynomial K) *
            ∏ i : Fin 4,
              a i ^
                ((d - (Finsupp.single kernel 1 : Fin 4 →₀ ℕ)) i) := by
          ring

/-- **Non-kernel derivative covariance for the concrete integral blow-up.** -/
theorem eval_pderiv_integralKernelBlowupFamily_kernelBlowupSection_of_ne
    (kernel i : Fin 4)
    (hi : i ≠ kernel)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a : Fin 4 → Polynomial K) :
    MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        (MvPolynomial.pderiv i
          (integralKernelBlowupFamily
            kernel slope P hdiv)) =
      MvPolynomial.eval a
        (MvPolynomial.pderiv i P) := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum P]
  unfold integralKernelBlowupFamily
  simp only [map_sum, MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hterm :=
    eval_pderiv_monomial_kernelBlowupSection_of_ne
      kernel i hi slope a d
      (kernelCoefficientQuotient
        kernel slope P hdiv d)
  rw [kernelCoefficientQuotient_spec_of_mem
    kernel slope P hdiv hd]
  exact hterm

/-- **Kernel derivative covariance for the concrete integral blow-up.**

The single external factor `τ^slope` is the chain-rule factor contributed
by the rescaled kernel source coordinate. -/
theorem eval_pderiv_integralKernelBlowupFamily_kernelBlowupSection_kernel
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a : Fin 4 → Polynomial K) :
    Polynomial.X ^ slope *
      MvPolynomial.eval
        (kernelBlowupSection kernel slope a)
        (MvPolynomial.pderiv kernel
          (integralKernelBlowupFamily
            kernel slope P hdiv)) =
      MvPolynomial.eval a
        (MvPolynomial.pderiv kernel P) := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum P]
  unfold integralKernelBlowupFamily
  simp only [map_sum, MvPolynomial.eval_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hterm :=
    eval_pderiv_monomial_kernelBlowupSection_kernel
      kernel slope a d
      (kernelCoefficientQuotient
        kernel slope P hdiv d)
  rw [kernelCoefficientQuotient_spec_of_mem
    kernel slope P hdiv hd]
  exact hterm

/-- Cancellation of a nonzero power of the polynomial parameter. -/
theorem polynomial_X_pow_mul_cancel
    (n : ℕ)
    {u v : Polynomial K}
    (h :
      Polynomial.X ^ n * u =
        Polynomial.X ^ n * v) :
    u = v := by
  have hX :
      (Polynomial.X ^ n : Polynomial K) ≠ 0 :=
    pow_ne_zero n Polynomial.X_ne_zero
  have hz :
      Polynomial.X ^ n * (u - v) = 0 := by
    rw [mul_sub, h, sub_self]
  have huv : u - v = 0 := by
    rcases mul_eq_zero.mp hz with hzero | hzero
    · exact False.elim (hX hzero)
    · exact hzero
  exact sub_eq_zero.mp huv

/-- **Exact family-gradient collision survives the concrete integral
kernel blow-up.**

This closes the collision-preservation part of the kernel-blow-up lemma:
all non-kernel gradient components transport exactly, while the kernel
component transports after cancelling the common nonzero factor
`τ^slope`. -/
theorem polynomialFamilyExactGradientCollision_integralKernelBlowup
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (integralKernelBlowupFamily
        kernel slope P hdiv)
      (kernelBlowupSection kernel slope a)
      (kernelBlowupSection kernel slope b) := by
  intro i
  by_cases hi : i = kernel
  · subst i
    apply polynomial_X_pow_mul_cancel
      (K := K) slope
    calc
      Polynomial.X ^ slope *
          MvPolynomial.eval
            (kernelBlowupSection kernel slope a)
            (MvPolynomial.pderiv kernel
              (integralKernelBlowupFamily
                kernel slope P hdiv)) =
        MvPolynomial.eval a
          (MvPolynomial.pderiv kernel P) :=
        eval_pderiv_integralKernelBlowupFamily_kernelBlowupSection_kernel
          kernel slope P hdiv a
      _ =
        MvPolynomial.eval b
          (MvPolynomial.pderiv kernel P) :=
        hcoll kernel
      _ =
        Polynomial.X ^ slope *
          MvPolynomial.eval
            (kernelBlowupSection kernel slope b)
            (MvPolynomial.pderiv kernel
              (integralKernelBlowupFamily
                kernel slope P hdiv)) :=
        (eval_pderiv_integralKernelBlowupFamily_kernelBlowupSection_kernel
          kernel slope P hdiv b).symm
  · rw [
      eval_pderiv_integralKernelBlowupFamily_kernelBlowupSection_of_ne
        kernel i hi slope P hdiv a,
      eval_pderiv_integralKernelBlowupFamily_kernelBlowupSection_of_ne
        kernel i hi slope P hdiv b]
    exact hcoll i

/-- The concrete integral blow-up therefore supplies the family-collision
field required by the Phase 93.51 restart certificate. -/
theorem integralKernelBlowup_hasPolynomialFamilyExactGradientCollision
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b) :
    HasPolynomialFamilyExactGradientCollision
      (integralKernelBlowupFamily
        kernel slope P hdiv)
      (kernelBlowupSection kernel slope a)
      (kernelBlowupSection kernel slope b) :=
  polynomialFamilyExactGradientCollision_integralKernelBlowup
    kernel slope P hdiv a b hcoll

end

end HC4.Valuation
