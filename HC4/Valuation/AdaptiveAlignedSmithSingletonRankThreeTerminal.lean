import HC4.Valuation.AdaptiveAlignedSmithVerticalEndpointNondegeneracy
import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture
import Mathlib.Tactic

/-!
# A18.5.15: a singular positive singleton Smith fibre is terminal rank three

A18.5.13 identifies the restriction to one exact Smith exponent `e=(b,c,d)`
with the honest vertical polynomial

    x₁^b x₂^c x₃^d * phi(x₀),

where `phi` is the longitudinal coefficient fibre of the source polynomial.
A18.5.14 shows that, once `b,c,d` are positive and this vertical polynomial is
Hessian-singular, the one-variable endpoint hypotheses needed by the mature
rank-three rational-rigidity stack are automatic.

The stationary Smith machinery already packages longitudinal motion as
`HasFirstExactSmithExponentLongitudinalDeparture`: two occupied coefficients
at orders `n` and `n+q`, with `q>0`.

This file composes those facts into the exact Newton-facing endpoint theorem.
A future face-extraction theorem only has to produce a *positive singleton
Smith fibre* whose Hessian determinant vanishes.  No denominator, degree,
constant-term, or coefficient-polynomial side condition remains.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Positive singular singleton Smith fibre -> polynomial rank-three
terminal certificate.** -/
theorem hasRankThreePolynomialTerminalCertificate_of_positive_singletonSmithFiber
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (hb : 0 < e.b) (hc : 0 < e.c) (hd : 0 < e.d)
    (hdeparture : HasFirstExactSmithExponentLongitudinalDeparture F e)
    (hdet :
      HC4.Polynomial.hessianDeterminant
        (smithSubfacePolynomial (1 : Fin 4) 2 3 {e} F) = 0) :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := longitudinalCoefficientPolynomial e.b e.c e.d F)
      (e.b : K) (e.c : K) (e.d : K) 1 0 0 0 := by
  rcases hdeparture with ⟨n, q, hq, hn, hnq, hbefore⟩
  have hvertical :
      HC4.Polynomial.hessianDeterminant
        (HC4.Polynomial.rankThreeVerticalPolynomial
          e.b e.c e.d
          (longitudinalCoefficientPolynomial e.b e.c e.d F)) = 0 := by
    rw [← smithSubfacePolynomial_singleton_eq_rankThreeVerticalPolynomial F e]
    exact hdet
  exact
    hasRankThreePolynomialTerminalCertificate_of_vertical_support_pair
      hb hc hd hq hn hnq hvertical

end

end HC4.Valuation
