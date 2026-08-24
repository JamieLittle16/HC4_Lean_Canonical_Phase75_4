import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurTransverseReesLayer
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurFirstKeyLeadingKernel
import HC4.Valuation.KernelInflationHessianDefect
import HC4.Valuation.ExactKernelDefectDrop
import Mathlib.Tactic

/-!
# Stage 4B34: polynomial Rees transport of the source-coordinate Hessian kernel

B33 identifies the transverse spatial filtration with the honest Rees
substitution

    x₀ |-> x₀,     xᵢ |-> τ xᵢ  (i = 1,2,3).

For the final first-departure argument we also need the corresponding kernel
vector.  The Hessian chain rule contributes one factor of `τ` in each
transverse row and column.  Therefore, if

    Hess(F) * W = 0,

the polynomial (not Laurent) vector

    W^R = (τ W₀(x₀,τx⊥), W₁(x₀,τx⊥), W₂(x₀,τx⊥), W₃(x₀,τx⊥))

satisfies

    Hess(F^R) * W^R = 0.

This is exactly the Rees-series incarnation of the derivative-shifted weight
used in B8.  No chart, Schur, or deformation-clock hypothesis occurs here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

variable {K : Type*} [Field K] [CharZero K]

/-- Chain-rule coefficient for the simultaneous unit transverse Rees
inflation. -/
def transverseReesDerivativeCoefficient (i : Fin 4) : Polynomial K :=
  if i = 0 then 1 else Polynomial.X

/-- Complementary polynomial kernel scaling.  It is chosen so that the
product with the derivative coefficient is always the common factor `X`. -/
def transverseReesKernelScale (i : Fin 4) : Polynomial K :=
  if i = 0 then Polynomial.X else 1

@[simp] theorem transverseReesDerivativeCoefficient_mul_kernelScale
    (i : Fin 4) :
    transverseReesDerivativeCoefficient (K := K) i *
        transverseReesKernelScale (K := K) i = Polynomial.X := by
  by_cases hi : i = 0
  · simp [transverseReesDerivativeCoefficient,
      transverseReesKernelScale, hi]
  · simp [transverseReesDerivativeCoefficient,
      transverseReesKernelScale, hi]

/-- Hessian commutes with embedding the source coefficients into the
parameter-polynomial coefficient ring. -/
theorem hessian_map_polynomialC_entry
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessian (MvPolynomial.map Polynomial.C F) i j =
      MvPolynomial.map Polynomial.C (HC4.Polynomial.hessian F i j) := by
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]

/-- Entrywise chain rule for the simultaneous transverse Rees substitution. -/
theorem hessian_transverseSourceReesFamily_entry
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessian (transverseSourceReesFamily F) i j =
      MvPolynomial.C
          (transverseReesDerivativeCoefficient (K := K) i *
            transverseReesDerivativeCoefficient (K := K) j) *
        transverseSourceReesFamily (HC4.Polynomial.hessian F i j) := by
  unfold transverseSourceReesFamily unitTransverseInflateFamily
  rw [hessian_kernelInflateHom_entry]
  rw [hessian_kernelInflateHom_entry]
  rw [hessian_kernelInflateHom_entry]
  rw [hessian_map_polynomialC_entry]
  simp only [map_mul, kernelInflateHom_C]
  fin_cases i <;> fin_cases j <;>
    simp [transverseReesDerivativeCoefficient,
      kernelInflateDerivativeCoefficient] <;> ring

/-- Rees transport is multiplicative. -/
theorem transverseSourceReesFamily_mul
    (P Q : MvPolynomial (Fin 4) K) :
    transverseSourceReesFamily (P * Q) =
      transverseSourceReesFamily P * transverseSourceReesFamily Q := by
  simp [transverseSourceReesFamily, unitTransverseInflateFamily, map_mul]

/-- Rees transport commutes with a finite sum. -/
theorem transverseSourceReesFamily_sum
    {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin 4) K) :
    transverseSourceReesFamily (∑ i, P i) =
      ∑ i, transverseSourceReesFamily (P i) := by
  simp [transverseSourceReesFamily, unitTransverseInflateFamily, map_sum]

/-- Polynomial Rees transform of a source-coordinate vector, with the
single complementary longitudinal factor needed to cancel the Hessian chain
rule. -/
noncomputable def transverseSourceReesKernel
    (W : Fin 4 → MvPolynomial (Fin 4) K) :
    Fin 4 → MvPolynomial (Fin 4) (Polynomial K) :=
  fun j =>
    MvPolynomial.C (transverseReesKernelScale (K := K) j) *
      transverseSourceReesFamily (W j)

/-- **Exact Rees kernel covariance.**

An honest source-coordinate polynomial Hessian kernel remains an honest
polynomial Hessian kernel after simultaneous transverse Rees inflation, once
the derivative-compatible complementary vector scaling is inserted. -/
theorem transverseSourceReesKernel_isKernel
    (F : MvPolynomial (Fin 4) K)
    (W : Fin 4 → MvPolynomial (Fin 4) K)
    (hkernel : (HC4.Polynomial.hessian F).mulVec W = 0) :
    (HC4.Polynomial.hessian (transverseSourceReesFamily F)).mulVec
        (transverseSourceReesKernel W) = 0 := by
  funext i
  have hrow :
      ∑ j : Fin 4, HC4.Polynomial.hessian F i j * W j = 0 := by
    have hi := congrFun hkernel i
    simpa [Matrix.mulVec, dotProduct] using hi
  rw [Matrix.mulVec]
  simp only [dotProduct, transverseSourceReesKernel,
    hessian_transverseSourceReesFamily_entry]
  calc
    ∑ j : Fin 4,
        (MvPolynomial.C
              (transverseReesDerivativeCoefficient (K := K) i *
                transverseReesDerivativeCoefficient (K := K) j) *
            transverseSourceReesFamily
              (HC4.Polynomial.hessian F i j)) *
          (MvPolynomial.C (transverseReesKernelScale (K := K) j) *
            transverseSourceReesFamily (W j)) =
        MvPolynomial.C
            (transverseReesDerivativeCoefficient (K := K) i * Polynomial.X) *
          (∑ j : Fin 4,
            transverseSourceReesFamily
              (HC4.Polynomial.hessian F i j * W j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [transverseSourceReesFamily_mul]
      calc
        (MvPolynomial.C
              (transverseReesDerivativeCoefficient (K := K) i *
                transverseReesDerivativeCoefficient (K := K) j) *
            transverseSourceReesFamily
              (HC4.Polynomial.hessian F i j)) *
          (MvPolynomial.C (transverseReesKernelScale (K := K) j) *
            transverseSourceReesFamily (W j)) =
            (MvPolynomial.C
                (transverseReesDerivativeCoefficient (K := K) i *
                  transverseReesDerivativeCoefficient (K := K) j) *
              MvPolynomial.C (transverseReesKernelScale (K := K) j)) *
              (transverseSourceReesFamily
                  (HC4.Polynomial.hessian F i j) *
                transverseSourceReesFamily (W j)) := by ring
        _ = MvPolynomial.C
              ((transverseReesDerivativeCoefficient (K := K) i *
                  transverseReesDerivativeCoefficient (K := K) j) *
                transverseReesKernelScale (K := K) j) *
              (transverseSourceReesFamily
                  (HC4.Polynomial.hessian F i j) *
                transverseSourceReesFamily (W j)) := by
            rw [← MvPolynomial.C_mul]
        _ = MvPolynomial.C
              (transverseReesDerivativeCoefficient (K := K) i * Polynomial.X) *
              (transverseSourceReesFamily
                  (HC4.Polynomial.hessian F i j) *
                transverseSourceReesFamily (W j)) := by
            have hscale :
                (transverseReesDerivativeCoefficient (K := K) i *
                    transverseReesDerivativeCoefficient (K := K) j) *
                  transverseReesKernelScale (K := K) j =
                    transverseReesDerivativeCoefficient (K := K) i *
                      Polynomial.X := by
              rw [mul_assoc,
                transverseReesDerivativeCoefficient_mul_kernelScale]
            rw [hscale]
    _ = MvPolynomial.C
          (transverseReesDerivativeCoefficient (K := K) i * Polynomial.X) *
        transverseSourceReesFamily
          (∑ j : Fin 4, HC4.Polynomial.hessian F i j * W j) := by
      rw [transverseSourceReesFamily_sum]
    _ = 0 := by
      rw [hrow]
      have hzero :
          transverseSourceReesFamily
              (0 : MvPolynomial (Fin 4) K) = 0 := by
        simp [transverseSourceReesFamily, unitTransverseInflateFamily]
      rw [hzero, mul_zero]

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

variable {degreeCap : ℕ}
variable {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}

/-- The B30-provenanced source-coordinate Stage-3 kernel therefore produces
an exact polynomial kernel series for the transverse Rees family.  This is
the series on which the final projective-departure calculation should be
performed; no chart comparison is needed. -/
theorem SourceCoordinateSpecialKernelData.reesKernel
    {C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B}
    (D : C.SourceCoordinateSpecialKernelData) :
    (HC4.Polynomial.hessian
        (transverseSourceReesFamily
          (polynomialFamilySpecialFiber C.family))).mulVec
      (transverseSourceReesKernel D.vector) = 0 := by
  exact transverseSourceReesKernel_isKernel
    (polynomialFamilySpecialFiber C.family) D.vector D.kernel

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
