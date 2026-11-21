import HC4.Valuation.AdaptiveAlignedSmithVerticalFiber
import HC4.RationalRigidity.RankThreeVerticalContradiction
import Mathlib.Tactic

/-!
# A18.5.18: a positive singleton Smith fibre is impossible

The Smith-facing form of the vertical rank-three contradiction is the one
needed by the terminal geometry.  If an exact singleton Smith restriction
has positive transverse exponent in all three Smith coordinates, its
longitudinal coefficient polynomial is nonconstant, and the restriction has
zero Hessian determinant, then the restriction is impossible.

A18.5.13 identifies the singleton restriction literally with the honest
vertical rank-three polynomial; A18.5.17 rules that polynomial out.  No new
geometric hypothesis is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **Positive singleton Smith contradiction.**

This is the direct adapter from exact Smith-fibre language to the now-closed
vertical rank-three branch. -/
theorem smithSingleton_hessian_impossible_of_positive
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (hb : 0 < e.b) (hc : 0 < e.c) (hd : 0 < e.d)
    (hphi :
      longitudinalCoefficientPolynomial e.b e.c e.d F ≠ 0)
    (hdeg :
      0 < (longitudinalCoefficientPolynomial e.b e.c e.d F).natDegree)
    (hdet :
      HC4.Polynomial.hessianDeterminant
        (smithSubfacePolynomial (1 : Fin 4) 2 3 {e} F) = 0) : False := by
  have hvertical :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeVerticalPolynomial
          e.b e.c e.d
          (longitudinalCoefficientPolynomial e.b e.c e.d F)) = 0 := by
    rw [← smithSubfacePolynomial_singleton_eq_rankThreeVerticalPolynomial]
    exact hdet
  exact
    HC4.RationalRigidity.rankThreeVertical_hessian_impossible_of_nonconstant
      hb hc hd hphi hdeg hvertical

end

end HC4.Valuation
