import HC4.Valuation.KernelInflationHessianDefect
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic

/-!
# Exact numerical defect drop for the integral kernel blow-up

Phase 93.56 proves the exact determinant factorisation

    det Hess(P)
      =
    tau^(2q) * Inflate_q(det Hess(Ptilde)).

This file extracts every remaining numerical consequence from that identity.

There are three steps.

1. Prove coefficientwise that kernel inflation does not mix source
   monomials:

       coeff_d(Inflate_q Q)
         =
       tau^(q*d(kernel)) * coeff_d(Q).

   Since the multiplier is nonzero, `Inflate_q` is injective.

2. If the source Hessian determinant is the pure parameter monomial
   `tau^Delta`, then the determinant factorisation itself implies

       2q <= Delta.

   Indeed `tau^(2q)` divides `tau^Delta`; comparing polynomial degrees gives
   the inequality.

3. Cancel `tau^(2q)` and use injectivity of `Inflate_q` to obtain

       det Hess(Ptilde) = tau^(Delta - 2q).

Thus a positive slope constructs `HasPositiveKernelDefectDrop` rather than
requiring it as an external hypothesis.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Coefficients and injectivity of kernel inflation -/

/-- Kernel inflation acts diagonally on a single source monomial. -/
theorem kernelInflateHom_monomial
    (kernel : Fin 4)
    (slope : ℕ)
    (d : Fin 4 →₀ ℕ)
    (c : Polynomial K) :
    kernelInflateHom (K := K) kernel slope
        (MvPolynomial.monomial d c) =
      MvPolynomial.monomial d
        (kernelCoefficientTauPower
          (K := K) kernel slope d * c) := by
  apply MvPolynomial.funext
  intro a
  rw [eval_kernelInflateHom]
  simp only [MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype
    d
    (fun n e =>
      kernelBlowupSection kernel slope a n ^ e)
    (by
      intro i
      simp)]
  rw [Finsupp.prod_fintype
    d
    (fun n e => a n ^ e)
    (by
      intro i
      simp)]
  rw [fin4_kernelBlowupSection_monomialProduct]
  ring

/-- **Coefficient formula for kernel inflation.**

Kernel inflation preserves the source exponent `d` and multiplies its
coefficient by exactly the expected power of the parameter. -/
theorem coeff_kernelInflateHom
    (kernel : Fin 4)
    (slope : ℕ)
    (Q : MvPolynomial (Fin 4) (Polynomial K))
    (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d
        (kernelInflateHom (K := K) kernel slope Q) =
      kernelCoefficientTauPower
          (K := K) kernel slope d *
        MvPolynomial.coeff d Q := by
  refine
    MvPolynomial.induction_on'
      (P := fun Q =>
        MvPolynomial.coeff d
            (kernelInflateHom (K := K) kernel slope Q) =
          kernelCoefficientTauPower
              (K := K) kernel slope d *
            MvPolynomial.coeff d Q)
      Q ?_ ?_
  · intro u c
    rw [kernelInflateHom_monomial]
    by_cases hud : u = d
    · subst u
      simp
    · have hdu : d ≠ u := Ne.symm hud
      simp [MvPolynomial.coeff_monomial, hud, hdu]
  · intro p q hp hq
    simp only [map_add, MvPolynomial.coeff_add]
    rw [hp, hq]
    ring

/-- **Kernel inflation is injective.**

No source monomials are merged, and every diagonal coefficient multiplier
is a nonzero power of `tau`. -/
theorem kernelInflateHom_injective
    (kernel : Fin 4)
    (slope : ℕ) :
    Function.Injective
      (kernelInflateHom (K := K) kernel slope) := by
  intro P Q hPQ
  apply MvPolynomial.ext
  intro d
  have hcoeff :=
    congrArg (MvPolynomial.coeff d) hPQ
  rw [
    coeff_kernelInflateHom,
    coeff_kernelInflateHom] at hcoeff
  let u : Polynomial K :=
    kernelCoefficientTauPower
      (K := K) kernel slope d
  have hu : u ≠ 0 := by
    unfold u kernelCoefficientTauPower
    exact
      pow_ne_zero
        (slope * d kernel)
        Polynomial.X_ne_zero
  have hz :
      u *
        (MvPolynomial.coeff d P -
          MvPolynomial.coeff d Q) = 0 := by
    rw [mul_sub, hcoeff, sub_self]
  rcases mul_eq_zero.mp hz with hzero | hsub
  · exact False.elim (hu hzero)
  · exact sub_eq_zero.mp hsub

/-! ## The factorisation forces `2q <= Delta` -/

/-- A pure source Hessian defect bounds every integral kernel slope by half
the source defect.

This is not an additional hypothesis: it follows from the determinant
factorisation itself. -/
theorem two_mul_slope_le_of_integralKernelBlowup
    (kernel : Fin 4)
    (slope Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    2 * slope ≤ Delta := by
  have hfactor :=
    integralKernelBlowup_defect_factor_equation
      kernel slope Delta P hdiv hdef
  have hdvdMv :
      MvPolynomial.C
          ((Polynomial.X ^ slope) ^ 2) ∣
        (MvPolynomial.C
          (Polynomial.X ^ Delta) :
          MvPolynomial (Fin 4) (Polynomial K)) := by
    refine
      ⟨kernelInflateHom (K := K) kernel slope
          (HC4.Polynomial.hessianDeterminant
            (integralKernelBlowupFamily
              kernel slope P hdiv)),
        ?_⟩
    simpa only [MvPolynomial.C_pow] using hfactor
  have hdvdPoly :
      (Polynomial.X ^ slope) ^ 2 ∣
        (Polynomial.X ^ Delta : Polynomial K) := by
    have hall :=
      (MvPolynomial.C_dvd_iff_dvd_coeff
        ((Polynomial.X ^ slope) ^ 2)
        (MvPolynomial.C
          (Polynomial.X ^ Delta) :
          MvPolynomial (Fin 4) (Polynomial K))).mp
        hdvdMv
    simpa only [MvPolynomial.coeff_zero_C] using
      (hall (0 : Fin 4 →₀ ℕ))
  have hpow :
      (Polynomial.X ^ slope) ^ 2 =
        (Polynomial.X ^ (2 * slope) :
          Polynomial K) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow] at hdvdPoly
  rcases hdvdPoly with ⟨R, hR⟩
  have hXR :
      R ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hR
    exact
      (pow_ne_zero Delta Polynomial.X_ne_zero)
        hR
  have hfactorNonzero :
      (Polynomial.X ^ (2 * slope) :
        Polynomial K) ≠ 0 :=
    pow_ne_zero (2 * slope) Polynomial.X_ne_zero
  have hdeg :
      Delta =
        2 * slope + R.natDegree := by
    calc
      Delta =
          (Polynomial.X ^ Delta :
            Polynomial K).natDegree := by
              simp
      _ =
          ((Polynomial.X ^ (2 * slope) :
            Polynomial K) * R).natDegree := by
              rw [hR]
      _ =
          (Polynomial.X ^ (2 * slope) :
            Polynomial K).natDegree +
              R.natDegree := by
                exact
                  Polynomial.natDegree_mul
                    hfactorNonzero hXR
      _ = 2 * slope + R.natDegree := by
            simp
  omega

/-! ## Exact target defect -/

/-- Pure parameter powers are fixed by kernel inflation. -/
theorem kernelInflateHom_C
    (kernel : Fin 4)
    (slope : ℕ)
    (c : Polynomial K) :
    kernelInflateHom (K := K) kernel slope
        (MvPolynomial.C c) =
      (MvPolynomial.C c :
        MvPolynomial (Fin 4) (Polynomial K)) := by
  simp [kernelInflateHom]

/-- **Exact Hessian defect of the integral kernel blow-up.**

If the source defect is `Delta`, the target defect is literally

    Delta - 2*slope.

The required inequality `2*slope <= Delta` is derived internally from the
green Phase 93.56 determinant factorisation. -/
theorem integralKernelBlowup_hasHessianDefect_sub
    (kernel : Fin 4)
    (slope Delta : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      (integralKernelBlowupFamily
        kernel slope P hdiv)
      (Delta - 2 * slope) := by
  let Ptilde :=
    integralKernelBlowupFamily
      kernel slope P hdiv
  let Htilde :=
    HC4.Polynomial.hessianDeterminant Ptilde
  let m := Delta - 2 * slope
  have hle :
      2 * slope ≤ Delta :=
    two_mul_slope_le_of_integralKernelBlowup
      kernel slope Delta P hdiv hdef
  have hfactor :=
    integralKernelBlowup_defect_factor_equation
      kernel slope Delta P hdiv hdef
  have hexp :
      2 * slope + m = Delta := by
    unfold m
    omega
  have hpoly :
      (Polynomial.X ^ slope) ^ 2 *
          Polynomial.X ^ m =
        (Polynomial.X ^ Delta :
          Polynomial K) := by
    calc
      (Polynomial.X ^ slope) ^ 2 *
          Polynomial.X ^ m =
        Polynomial.X ^ (2 * slope) *
          Polynomial.X ^ m := by
            congr 1
            rw [← pow_mul]
            congr 1
            omega
      _ =
        Polynomial.X ^ (2 * slope + m) := by
          rw [pow_add]
      _ =
        Polynomial.X ^ Delta := by
          rw [hexp]
  have hconst :
      (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
        MvPolynomial.C
          (Polynomial.X ^ m) =
      MvPolynomial.C
        (Polynomial.X ^ Delta) := by
    rw [← MvPolynomial.C_pow,
        ← MvPolynomial.C_mul,
        hpoly]
  have hcancel :
      (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
        MvPolynomial.C
          (Polynomial.X ^ m) =
      (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
        kernelInflateHom (K := K) kernel slope Htilde := by
    calc
      (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
        MvPolynomial.C
          (Polynomial.X ^ m) =
        MvPolynomial.C
          (Polynomial.X ^ Delta) := hconst
      _ =
        (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
        kernelInflateHom (K := K) kernel slope Htilde := by
          simpa [Htilde, Ptilde] using hfactor
  have hbase :
      (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ≠ 0 := by
    exact
      MvPolynomial.C_ne_zero.mpr
        (pow_ne_zero slope Polynomial.X_ne_zero)
  have hfac :
      (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hbase
  have hz :
      (MvPolynomial.C
          (Polynomial.X ^ slope) :
          MvPolynomial (Fin 4) (Polynomial K)) ^ 2 *
        (MvPolynomial.C
            (Polynomial.X ^ m) -
          kernelInflateHom (K := K)
            kernel slope Htilde) = 0 := by
    rw [mul_sub, hcancel, sub_self]
  have hinflated :
      kernelInflateHom (K := K)
          kernel slope Htilde =
        MvPolynomial.C
          (Polynomial.X ^ m) := by
    rcases mul_eq_zero.mp hz with hzero | hsub
    · exact False.elim (hfac hzero)
    · exact (sub_eq_zero.mp hsub).symm
  have himages :
      kernelInflateHom (K := K)
          kernel slope Htilde =
        kernelInflateHom (K := K)
          kernel slope
          (MvPolynomial.C
            (Polynomial.X ^ m)) := by
    rw [hinflated, kernelInflateHom_C]
  have htarget :
      Htilde =
        MvPolynomial.C
          (Polynomial.X ^ m) :=
    kernelInflateHom_injective
      (K := K) kernel slope himages
  simpa [HasPolynomialFamilyHessianDefect,
    Htilde, Ptilde, m] using htarget

/-! ## Automatic global defect-drop certificate -/

/-- Construct the arithmetic global restart certificate directly from the
source/target polynomial defects and a positive kernel slope. -/
theorem integralKernelBlowup_positiveKernelDefectDrop
    {s t : GlobalRestartState}
    (kernel : Fin 4)
    {slope Delta : ℕ}
    (hslope : 0 < slope)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (hs :
      s.defect = Delta)
    (ht :
      t.defect = Delta - 2 * slope) :
    HasPositiveKernelDefectDrop
      slope s t := by
  have hle :
      2 * slope ≤ Delta :=
    two_mul_slope_le_of_integralKernelBlowup
      kernel slope Delta P hdiv hdef
  exact
    ⟨hslope,
      by
        rw [hs]
        exact hle,
      by
        rw [ht, hs]⟩

/-- **End-to-end positive-slope restart with no assumed defect-drop
certificate.**

The concrete integral blow-up itself now proves both:
- the target Hessian defect `Delta - 2q`;
- the arithmetic `HasPositiveKernelDefectDrop`.

The only remaining inputs are the genuinely geometric data: positive slope,
coefficient divisibility, exact collision, and distinct transformed special
points. -/
theorem integralKernelBlowup_exactDefect_and_strictRestart
    {s t : GlobalRestartState}
    (kernel : Fin 4)
    {slope Delta : ℕ}
    (hslope : 0 < slope)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (hdef :
      HasPolynomialFamilyHessianDefect
        (K := K) P Delta)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (hspecialDistinct :
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b))
    (hs :
      s.defect = Delta)
    (ht :
      t.defect = Delta - 2 * slope) :
    HasPolynomialFamilyHessianDefect
        (K := K)
        (integralKernelBlowupFamily
          kernel slope P hdiv)
        (Delta - 2 * slope) ∧
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b) ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily
            kernel slope P hdiv))
        (polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a))
        (polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b)) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  have htarget :=
    integralKernelBlowup_hasHessianDefect_sub
      kernel slope Delta P hdiv hdef
  have hdrop :=
    integralKernelBlowup_positiveKernelDefectDrop
      kernel hslope P hdiv hdef hs ht
  have hrestart :=
    integralKernelBlowup_preservesSpecialCollision_and_strictlyRestarts
      kernel slope P hdiv a b
      hcoll hspecialDistinct hdrop
  exact
    ⟨htarget,
      hrestart.1,
      hrestart.2.1,
      hrestart.2.2.1,
      hrestart.2.2.2⟩

end

end HC4.Valuation
