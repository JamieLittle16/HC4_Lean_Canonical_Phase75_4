import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import Mathlib.Tactic

/-!
# A18.4.64: kernel-linear first contact already contains mixed Hessian geometry

The saturated first-contact theorem historically separated a supported
monomial with kernel exponent one from the exponent-at-least-two case.  The
former was sent to unramified defect descent; the latter supplied a nonzero
diagonal Hessian entry.

For the canonical HC4 families there is stronger information: the relevant
source family has zero linear source jet.  A supported monomial whose kernel
exponent is exactly one therefore cannot be the lone linear monomial
`X_kernel`.  Some other source coordinate occurs positively, and
characteristic-zero coefficient calculus makes the corresponding mixed
Hessian derivative nonzero.

This file isolates that purely algebraic fact.  It uses the existing
`coeff_pderiv_backport` / `exponent_eq_zero_of_pderiv_eq_zero` engine from
`CharZeroHessianKernelRigidity`, so no new analytic input is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A supported kernel-linear monomial in a polynomial with no source-linear
terms must use some second source coordinate. -/
theorem exists_other_positive_exponent_of_supported_kernel_linear
    (F : MvPolynomial (Fin 4) K)
    (hlinear :
      ∀ i : Fin 4,
        MvPolynomial.coeff (Finsupp.single i 1) F = 0)
    (kernel : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hkernel : d kernel = 1) :
    ∃ j : Fin 4, j ≠ kernel ∧ 0 < d j := by
  by_cases hex : ∃ j : Fin 4, j ≠ kernel ∧ 0 < d j
  · exact hex
  · have hzero : ∀ j : Fin 4, j ≠ kernel → d j = 0 := by
      intro j hj
      have hnot : ¬ 0 < d j := by
        intro hpos
        exact hex ⟨j, hj, hpos⟩
      exact Nat.eq_zero_of_not_pos hnot
    have hdeq : d = Finsupp.single kernel 1 := by
      ext j
      by_cases hj : j = kernel
      · subst j
        simp [hkernel]
      · simp [Finsupp.single_apply, hj, hzero j hj]
    have hcoeff : MvPolynomial.coeff d F ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    rw [hdeq] at hcoeff
    exact (hcoeff (hlinear kernel)).elim

/-- A supported monomial containing two distinct variables positively forces
the corresponding mixed Hessian derivative to be nonzero in characteristic
zero. -/
theorem pderiv_pderiv_ne_zero_of_support_exponents_pos
    (i j : Fin 4)
    (hij : i ≠ j)
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hi : 0 < d i)
    (hj : 0 < d j) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i F) ≠ 0 := by
  intro hzero
  let m : Fin 4 →₀ ℕ := d - Finsupp.single i 1
  have hi0 : d i ≠ 0 := Nat.ne_of_gt hi
  have hmadd : m + Finsupp.single i 1 = d := by
    dsimp [m]
    exact Finsupp.sub_add_single_one_cancel hi0
  have hcoeff :
      MvPolynomial.coeff m (MvPolynomial.pderiv i F) ≠ 0 := by
    rw [coeff_pderiv_backport]
    rw [hmadd]
    have hdcoeff : MvPolynomial.coeff d F ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have hcast : (((m i + 1 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (m i)
    exact mul_ne_zero hdcoeff hcast
  have hmj : m j = d j := by
    dsimp [m]
    have hji : j ≠ i := Ne.symm hij
    simp [Finsupp.single_apply, hji]
  have hmj0 : m j = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero
      j (MvPolynomial.pderiv i F) hzero m hcoeff
  rw [hmj] at hmj0
  omega

/-- The two possible Hessian signatures created by a positive kernel first
contact once source-linear terms are absent. -/
inductive AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
    (F : MvPolynomial (Fin 4) K)
    (kernel : Fin 4) : Prop
  | diagonal
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ F.support)
      (hkernel : 2 ≤ d kernel)
      (hne :
        MvPolynomial.pderiv kernel
          (MvPolynomial.pderiv kernel F) ≠ 0)
  | mixed
      (d : Fin 4 →₀ ℕ)
      (hd : d ∈ F.support)
      (j : Fin 4)
      (hjk : j ≠ kernel)
      (hkernel : d kernel = 1)
      (hj : 0 < d j)
      (hne :
        MvPolynomial.pderiv j
          (MvPolynomial.pderiv kernel F) ≠ 0)

/-- **Positive first contact plus zero linear jet always produces Hessian
geometry.**

Exponent at least two gives the existing diagonal Hessian witness.  Exponent
one cannot be a lone linear source monomial, hence gives a nonzero mixed
Hessian entry with another source direction. -/
theorem firstContactHessianGeometry_of_linearCoeff_zero
    (F : MvPolynomial (Fin 4) K)
    (hlinear :
      ∀ i : Fin 4,
        MvPolynomial.coeff (Finsupp.single i 1) F = 0)
    (kernel : Fin 4)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hpos : 0 < d kernel) :
    AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry F kernel := by
  by_cases h1 : d kernel = 1
  · rcases exists_other_positive_exponent_of_supported_kernel_linear
        F hlinear kernel d hd h1 with ⟨j, hjk, hj⟩
    exact .mixed d hd j hjk h1 hj
      (pderiv_pderiv_ne_zero_of_support_exponents_pos
        kernel j (Ne.symm hjk) F d hd hpos hj)
  · have h2 : 2 ≤ d kernel := by omega
    exact .diagonal d hd h2
      (pderiv_pderiv_ne_zero_of_support_exponent_ge_two
        (K := K) kernel F d hd h2)

end

end HC4.Valuation
