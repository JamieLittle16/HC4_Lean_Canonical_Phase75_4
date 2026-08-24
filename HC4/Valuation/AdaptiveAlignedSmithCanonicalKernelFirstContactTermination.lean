import HC4.Valuation.AdaptiveAlignedSmithCanonicalRamifiedUnramifiedReentry
import HC4.Newton.CharZeroHessianKernelRigidity
import Mathlib.Tactic

/-!
# A18.4.39: saturated kernel contact is unramified or Hessian-active

The final presentation-free exact-clock frontier still contains honest
ramified raw-defect spends.  A bare rational decrease across changing scales
is not, by itself, a valid well-founded recursive coordinate.

The geometry which creates these spends is stronger.  Before the saturated
kernel opening the special fibre is independent of a genuine transverse
coordinate.  The denominator-cleared first-contact face then contains an
actual monomial with positive exponent in that coordinate.

This file records the exact dichotomy needed by the global termination pass.

* If one exposed first-contact monomial is kernel-linear, the already-green
  unramified re-entry theorem converts the opening into literal same-scale
  strict progress.
* Otherwise an exposed monomial has kernel exponent at least two.  In
  characteristic zero its second kernel derivative is nonzero, so the new
  special fibre carries genuine Hessian activity in the previously free
  direction.

No recursive progress is asserted in the second branch here.  The point is to
retain the geometric event rather than erase it into a numerical ramified
spend certificate.  The following assembly can consume that Hessian activity
through the finite rank ladder.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A supported monomial of exponent at least two in one coordinate forces
that diagonal Hessian entry to be a nonzero polynomial.

This is deliberately stated for an arbitrary multivariable polynomial.  The
proof uses only characteristic-zero coefficient calculus and therefore does
not depend on any Smith or homogeneity hypothesis. -/
theorem pderiv_pderiv_ne_zero_of_support_exponent_ge_two
    (kernel : Fin 4)
    (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ F.support)
    (hd2 : 2 ≤ d kernel) :
    MvPolynomial.pderiv kernel (MvPolynomial.pderiv kernel F) ≠ 0 := by
  intro hzero
  let d₁ : Fin 4 →₀ ℕ := d - Finsupp.single kernel 1
  have hdk : d kernel ≠ 0 := by omega
  have hadd : d₁ + Finsupp.single kernel 1 = d := by
    dsimp [d₁]
    exact Finsupp.sub_add_single_one_cancel hdk
  have hdne : MvPolynomial.coeff d F ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hd₁coeff :
      MvPolynomial.coeff d₁ (MvPolynomial.pderiv kernel F) ≠ 0 := by
    rw [coeff_pderiv_backport]
    rw [hadd]
    apply mul_ne_zero hdne
    exact_mod_cast Nat.succ_ne_zero (d₁ kernel)
  have hd₁zero : d₁ kernel = 0 :=
    exponent_eq_zero_of_pderiv_eq_zero
      kernel (MvPolynomial.pderiv kernel F) hzero d₁ hd₁coeff
  have haddk := congrArg (fun e : Fin 4 →₀ ℕ => e kernel) hadd
  simp [hd₁zero] at haddk
  omega

/-- **Saturated first-contact termination dichotomy.**

For a scale-aware state whose special fibre is free of a genuine transverse
kernel coordinate, the canonical saturated opening cannot be an anonymous
cross-scale move.

Either a kernel-linear first-contact monomial exists, in which case the
opening unramifies to an honest same-scale strict successor of the original
state, or the saturated special fibre has a nonzero diagonal Hessian entry in
the newly opened coordinate.

The nonlinear branch retains an actual supported monomial as provenance for
that Hessian activity. -/
theorem ScaleAwareAdaptiveGeometricRestartState.saturatedKernelOpening_unramified_or_nonlinearHessian
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (kernel : Fin 4)
    (hkernel : kernel ≠ (0 : Fin 4))
    (hactive : IsActiveKernelCoordinate kernel s.family)
    (hfree :
      ∀ d ∈ (polynomialFamilySpecialFiber s.family).support,
        d kernel = 0) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedSameScaleEpisodeProgress RR target s) ∨
      let R := kernelSlopeDenominatorClearingRamification kernel s.family
      let q := saturatedKernelSlope kernel s.family hactive
      let Pram := parameterRamificationFamily (K := K) R s.family
      let hdiv := saturatedKernelSlope_divisibility_afterRamification
        (K := K) kernel s.family hactive
      let Fnext := polynomialFamilySpecialFiber
        (integralKernelBlowupFamily kernel q Pram hdiv)
      ∃ d ∈ Fnext.support,
        2 ≤ d kernel ∧
        MvPolynomial.pderiv kernel (MvPolynomial.pderiv kernel Fnext) ≠ 0 := by
  let R := kernelSlopeDenominatorClearingRamification kernel s.family
  let q := saturatedKernelSlope kernel s.family hactive
  let Pram := parameterRamificationFamily (K := K) R s.family
  let hdiv := saturatedKernelSlope_divisibility_afterRamification
    (K := K) kernel s.family hactive
  let Fnext := polynomialFamilySpecialFiber
    (integralKernelBlowupFamily kernel q Pram hdiv)

  rcases specialFiber_saturatedKernelBlowup_active
      (K := K) kernel s.family hactive with ⟨d, hd, hdpos⟩
  by_cases hd1 : d kernel = 1
  · left
    exact s.exists_unramifiedReentry_of_saturatedLinearFirstContact
      RR kernel hkernel hactive hfree d
      (by simpa [R, q, Pram, hdiv, Fnext] using hd) hd1
  · right
    dsimp only
    have hd2 : 2 ≤ d kernel := by omega
    refine ⟨d, ?_, hd2, ?_⟩
    · simpa [R, q, Pram, hdiv, Fnext] using hd
    · apply pderiv_pderiv_ne_zero_of_support_exponent_ge_two
        (K := K) kernel Fnext d
      · simpa [R, q, Pram, hdiv, Fnext] using hd
      · exact hd2

end

end HC4.Valuation
