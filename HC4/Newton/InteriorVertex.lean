import HC4.Polynomial.MonomialHessian
import HC4.Polynomial.MaximalHessianInitial

/-!
# Interior vertices cannot occur on a zero-Hessian exposed face

If an exact maximal initial form of a zero-Hessian polynomial consists of a
single nonlinear monomial, then that monomial must lie on the boundary of the
toric exponent cone.  Otherwise all four exponents are positive, and the
monomial Hessian determinant is nonzero in characteristic zero.

This is the formal version of the interior-vertex sentence in Proposition 6.2.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

/-- A monomial exposed as a maximal exact initial form of a zero-Hessian
polynomial must omit a coordinate. -/
theorem exposed_monomial_on_boundary_of_zero_hessian
    {K : Type*} [Field K] [CharZero K]
    {F : MvPolynomial (Fin 4) K}
    {w : Fin 4 → ℤ} {level : ℤ}
    {d : Fin 4 →₀ ℕ} {c : K}
    (hbound : IsWeightLE w level F)
    (hzero : hessianDeterminant F = 0)
    (hinit : initialForm w level F = MvPolynomial.monomial d c)
    (hc : c ≠ 0)
    (hdeg : 3 ≤ ordinaryDegree4 d) :
    MvExponentOnBoundary d := by
  by_contra hboundary
  have hpos : ∀ i : Fin 4, 0 < d i :=
    coordinate_pos_of_not_mvExponentOnBoundary hboundary
  have hzinit : hessianDeterminant (initialForm w level F) = 0 :=
    hessianDeterminant_initialForm_eq_zero_of_eq_zero w level F hbound hzero
  rw [hinit] at hzinit
  exact (hessianDeterminant_monomial_ne_zero hc hpos hdeg) hzinit

end

end HC4.Newton
