import HC4.Valuation.AdaptiveAlignedSmithVerticalTerminal
import HC4.RationalRigidity.RankThreeVerticalContradiction
import Mathlib.Tactic

/-!
# A18.5.18: a genuine singular singleton Smith fibre is impossible

A18.5.15 connected one positive transverse Smith exponent with a genuine
later longitudinal layer to the rank-three polynomial terminal certificate.
A18.5.17 strengthens the vertical rank-three endpoint itself: every
nonconstant positive vertical line with zero Hessian determinant is
contradictory by the positive-reciprocal quadratic autonomous ODE.

This file composes those two facts at the Smith-facing interface.  The
terminal geometry no longer needs to mention rational functions or an
intermediate certificate.  It only has to produce

* a positive transverse Smith exponent;
* a genuine first later longitudinal layer over that exponent; and
* singularity of the exact singleton Smith restriction.

Those three concrete geometric facts are already enough for `False`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **A positive singular singleton Smith fibre with a genuine longitudinal
 departure cannot occur.** -/
theorem impossible_of_singular_singletonSmithFiber
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (hb : 0 < e.b) (hc : 0 < e.c) (hd : 0 < e.d)
    (hdeparture : HasFirstExactSmithExponentLongitudinalDeparture F e)
    (hsingular :
      HC4.Polynomial.hessianDeterminant
        (smithSubfacePolynomial (1 : Fin 4) 2 3 {e} F) = 0) : False := by
  let phi := longitudinalCoefficientPolynomial e.b e.c e.d F
  have hphi : phi ≠ 0 := by
    dsimp [phi]
    exact hdeparture.coefficientFiber_ne_zero
  have hdeg : 0 < phi.natDegree := by
    dsimp [phi]
    exact hdeparture.coefficientFiber_natDegree_pos
  have hvertical :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeVerticalPolynomial e.b e.c e.d phi) = 0 := by
    rw [← smithSubfacePolynomial_singleton_eq_rankThreeVerticalPolynomial]
    exact hsingular
  exact
    HC4.RationalRigidity.rankThreeVertical_hessian_impossible_of_nonconstant
      hb hc hd hphi hdeg hvertical

end

end HC4.Valuation
