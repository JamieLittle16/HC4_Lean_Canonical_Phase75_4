import HC4.Valuation.QuadraticTransverseCapSourcePolynomialFibre
import Mathlib.Tactic

/-!
# Exact moving-fibre equation for the ACTUAL quadratic-cap gradient

A fixed transverse-gradient output p has a polynomial preimage fibre
  y_p(X) = C(X)⁻¹(p-b(X))
in the regular branch. Since the actual transverse gradients are
constant along this fibre, the formal source chain rule yields

  v_i(X) + ∑_j C_ij(X) y_p,j'(X) = 0,

where v_i(X) is the ACTUAL mixed source Hessian H_{0,i} evaluated
at (X,y_p(X)).

This is the genuinely source-level, non-assumed identity needed
to compute the longitudinal Schur-complement slope. All equations
are polynomial identities in K[X], not analytic derivatives.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

/-- For the original determinant-one, cap-two potential in the
regular transverse-rank branch, construct a polynomial fibre
with constant transverse gradient and establish its true
moving-fibre Hessian equation, without a replacement source. -/
theorem quadraticTransverseCapSource_regularPolynomialFibre_drift
    (F : MvPolynomial (Fin 4) K)
    (hcap : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hregular :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore ≠ 0)
    (p : Fin 3 → K) :
    ∃ y : Fin 3 → Polynomial K,
      (∀ i : Fin 3,
        sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
          (MvPolynomial.pderiv i.succ F) = Polynomial.C (p i)) ∧
      (∀ i : Fin 3,
        sourcePolynomialPathSubstitution (Fin.cons Polynomial.X y)
          (HC4.Polynomial.hessian F 0 i.succ) +
          (∑ j : Fin 3,
            ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) *
              Polynomial.derivative (y j)) = 0) := by
  classical
  obtain ⟨y, hgrad⟩ :=
    quadraticTransverseCapSource_regularPolynomialFibre_gradient
      F hcap hdet hregular p
  refine ⟨y, hgrad, ?_⟩
  intro i
  let q := Fin.cons Polynomial.X y
  have hcomm :
      sourcePolynomialPathSubstitution q
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv i.succ F)) =
        sourcePolynomialPathSubstitution q
          (HC4.Polynomial.hessian F 0 i.succ) := by
    congr 1
    exact pderiv_comm_commRing (0 : Fin 4) i.succ F
  have hC (j : Fin 3) :
      sourcePolynomialPathSubstitution q
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ F)) =
        (quadraticTransverseCapSourceAxisThreeBlock F).matrix i j := by
    exact quadraticTransverseCapSource_polynomialPath_transverseHessian
      F hcap y i j
  have hsum :
      (∑ j : Fin 3, Polynomial.derivative (y j) *
          sourcePolynomialPathSubstitution q
            (MvPolynomial.pderiv j.succ
              (MvPolynomial.pderiv i.succ F))) =
        (∑ j : Fin 3,
          ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) *
            Polynomial.derivative (y j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hC j]
    ring
  have hchain :=
    sourcePolynomialLongitudinalSection_derivative
      (MvPolynomial.pderiv i.succ F) y
  rw [hgrad i] at hchain
  simp only [Polynomial.derivative_C] at hchain
  rw [hcomm, hsum] at hchain
  exact hchain.symm

end

end HC4.Valuation
