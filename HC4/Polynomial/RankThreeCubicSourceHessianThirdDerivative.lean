import HC4.Polynomial.RankThreeCubicSourceFractionKernel
import HC4.Polynomial.RankThreeCubicJacobiDetPderiv
import Mathlib.Tactic

/-!
# Actual source third derivatives are transverse Hessian derivatives

The cubic source has an honest polynomial transverse Hessian on every
longitudinal slice. Differentiating that Hessian entry with respect to
a transverse variable commutes with longitudinal specialization.
Commutation of polynomial partial derivatives then identifies it
exactly with the third derivative used in source quadratic transport.

This source-to-matrix identity is the derivative-level bridge needed
before applying Jacobi to a cubic Cramer residue. It has no extra
source, pole or chart assumptions.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

/-- The entries of the transverse derivative of the genuine source
Hessian are the corresponding specialized third source derivatives,
with the same derivative order as in the quadratic transport family. -/
theorem sourceTransverseHessian_pderiv_eq_third
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (i j k : Fin 3) :
    pderiv i (sourceTransverseHessian a L j k) =
      referenceSlice a
        (pderiv (.inr k) (pderiv (.inr j) (pderiv (.inr i) L))) := by
  change pderiv i (referenceSlice a
      (pderiv (.inr k) (pderiv (.inr j) L))) = _
  rw [referenceSlice_pderiv]
  rw [MvPolynomial.pderiv_comm (.inr i) (.inr k)
    (pderiv (.inr j) L)]
  rw [MvPolynomial.pderiv_comm (.inr i) (.inr j) L]

end
end HC4.Polynomial.RankThreeCubic
