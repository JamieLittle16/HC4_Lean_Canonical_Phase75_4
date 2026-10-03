import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurTransverseReesLayer
import HC4.Valuation.KernelInflationHessianDefect
import Mathlib.Tactic

/-!
# A19.R12: Hessian chain rule for transverse Rees inflation

A19.123 uses the simultaneous transverse inflation

    x₀ ↦ x₀,     xᵢ ↦ τ xᵢ  (i = 1,2,3)

to turn the contact grading into the pure binary grading `D - r*n`.
For the closing staircase adapter we need the corresponding source-Hessian
chain rule.  Each transverse source derivative contributes one factor of the
Rees parameter, while a longitudinal derivative contributes none.

This file records exactly that entrywise statement.  It is the small,
generic part of an earlier experimental B34 kernel module that compiled before
that experiment later failed in unrelated kernel-sum algebra.  No kernel,
Schur, or HC4-specific geometric assertion is included here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Chain-rule coefficient for one source derivative under simultaneous unit
transverse Rees inflation. -/
def transverseReesDerivativeCoefficient (i : Fin 4) : Polynomial K :=
  if i = 0 then 1 else Polynomial.X

@[simp] theorem transverseReesDerivativeCoefficient_zero :
    transverseReesDerivativeCoefficient (K := K) (0 : Fin 4) = 1 := by
  simp [transverseReesDerivativeCoefficient]

@[simp] theorem transverseReesDerivativeCoefficient_succ (i : Fin 3) :
    transverseReesDerivativeCoefficient (K := K) i.succ = Polynomial.X := by
  simp [transverseReesDerivativeCoefficient]

/-- Hessian commutes with embedding source coefficients into the parameter
polynomial coefficient ring. -/
theorem hessian_map_polynomialC_entry
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessian (MvPolynomial.map Polynomial.C F) i j =
      MvPolynomial.map Polynomial.C (HC4.Polynomial.hessian F i j) := by
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]

/-- **Exact transverse-Rees Hessian chain rule.**

The ordinary source Hessian of the transversely inflated family is the Rees
transform of the original Hessian entry multiplied by the two derivative
chain-rule factors. -/
theorem hessian_transverseSourceReesFamily_entry
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessian (transverseSourceReesFamily F) i j =
      MvPolynomial.C
          (transverseReesDerivativeCoefficient (K := K) i *
            transverseReesDerivativeCoefficient (K := K) j) *
        transverseSourceReesFamily (HC4.Polynomial.hessian F i j) := by
  unfold transverseSourceReesFamily unitTransverseInflateFamily
  simp only [hessian_kernelInflateHom_entry,
    hessian_map_polynomialC_entry, kernelInflateHom_C]
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · subst i
    subst j
    simp [transverseReesDerivativeCoefficient,
      kernelInflateDerivativeCoefficient]
  · subst i
    fin_cases j <;>
      simp_all [transverseReesDerivativeCoefficient,
        kernelInflateDerivativeCoefficient] <;> ring
  · subst j
    fin_cases i <;>
      simp_all [transverseReesDerivativeCoefficient,
        kernelInflateDerivativeCoefficient] <;> ring
  · fin_cases i <;> fin_cases j <;>
      simp_all [transverseReesDerivativeCoefficient,
        kernelInflateDerivativeCoefficient] <;> ring

end

end HC4.Valuation
