import HC4.Valuation.QuadraticTransverseCapSourceThirdDerivatives
import Mathlib.Tactic

/-!
# Transverse derivative-zero implies exact longitudinal support

This is the missing source-honest step between the already-green
third-transverse-derivative theorem and the section-independent
transverse Hessian block.

For a characteristic-zero field, a polynomial whose partial derivative
in transverse coordinate j vanishes has no nonzero-support exponent
in coordinate j. The proof uses the exact coefficient formula, so
it does not assume that a vanishing derivative automatically means
transverse independence in positive characteristic.

Applying this to the actual represented quadratic-cap source after two
transverse derivatives shows that EVERY source support exponent in
each transverse Hessian entry has zero transverse coordinates.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A vanishing partial derivative eliminates every positive exponent
of that variable from the support of a source polynomial. -/
theorem zeroPartial_sourceSupport_coordinate_zero
    (Q : MvPolynomial (Fin 4) K)
    (j : Fin 4)
    (hzero : MvPolynomial.pderiv j Q = 0)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ Q.support) :
    d j = 0 := by
  by_contra hn
  let m : Fin 4 →₀ ℕ := d - Finsupp.single j 1
  have hshift : m + Finsupp.single j 1 = d := by
    exact Finsupp.sub_add_single_one_cancel hn
  have hcoef :
      MvPolynomial.coeff m (MvPolynomial.pderiv j Q) = 0 := by
    rw [hzero]
    rfl
  rw [MvPolynomial.coeff_pderiv, hshift] at hcoef
  have hfactor : ((m j + 1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (m j))
  have hsource : MvPolynomial.coeff d Q = 0 :=
    (mul_eq_zero.mp hcoef).resolve_right hfactor
  exact (MvPolynomial.mem_support_iff.mp hd) hsource

/-- The genuine transverse Hessian block of a quadratic-cap source
has only longitudinal support: the three transverse exponents of
every nonzero monomial all vanish. -/
theorem transverseCapTwo_sourceHessian_support_longitudinal
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j : Fin 3)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ (HC4.Polynomial.hessian F i.succ j.succ).support)
    (k : Fin 3) :
    d k.succ = 0 := by
  exact zeroPartial_sourceSupport_coordinate_zero
    (HC4.Polynomial.hessian F i.succ j.succ)
    k.succ
    (transverseCapTwo_transverseHessian_pderiv_zero F hbound i j k)
    d hd

end

end HC4.Valuation
