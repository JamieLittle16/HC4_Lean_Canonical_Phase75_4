import HC4.Valuation.AdaptiveAlignedSmithVerticalEndpoint
import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture
import HC4.RationalRigidity.RankThreeVerticalLineTerminal
import Mathlib.Tactic

/-!
# A18.5.15: singular singleton Smith fibre gives the rank-three terminal

The remaining Smith-facing inputs are now entirely geometric.
For one exact transverse Smith exponent `e=(b,c,d)` assume:

* `b,c,d` are positive;
* the honest source has a genuine first later longitudinal layer over `e`;
* the singleton Smith restriction at `e` has zero Hessian determinant.

A18.5.13 identifies that singleton restriction with the honest vertical line
built from the longitudinal coefficient polynomial `φ`.  The first departure
makes `φ` nonzero and positive-degree.  A18.5.14 forces `φ(0) ≠ 0` from
singularity and transverse positivity.  A18.5.12 then supplies the complete
polynomial rank-three terminal certificate.

Thus after this file the rational endpoint is no longer visible to the Smith
geometry: it need only prove singularity of one exact singleton fibre (or take
the complementary-edge alternative).
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace HasFirstExactSmithExponentLongitudinalDeparture

/-- A first positive later longitudinal layer makes the exact coefficient
fibre nonzero. -/
theorem coefficientFiber_ne_zero
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasFirstExactSmithExponentLongitudinalDeparture F e) :
    longitudinalCoefficientPolynomial e.b e.c e.d F ≠ 0 := by
  rcases h with ⟨n, q, hq, hn, hnq, hbefore⟩
  intro hzero
  rw [hzero] at hn
  simp at hn

/-- A first positive later longitudinal layer forces positive natural degree of
the exact coefficient fibre. -/
theorem coefficientFiber_natDegree_pos
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    (h : HasFirstExactSmithExponentLongitudinalDeparture F e) :
    0 < (longitudinalCoefficientPolynomial e.b e.c e.d F).natDegree := by
  rcases h with ⟨n, q, hq, hn, hnq, hbefore⟩
  have hmem :
      n + q ∈
        (longitudinalCoefficientPolynomial e.b e.c e.d F).support :=
    Polynomial.mem_support_iff.mpr hnq
  have hle :
      n + q ≤
        (longitudinalCoefficientPolynomial e.b e.c e.d F).natDegree :=
    Polynomial.le_natDegree_of_mem_supp _ hmem
  omega

end HasFirstExactSmithExponentLongitudinalDeparture

/-- **Singular singleton Smith fibre closes through the rank-three rational
rigidity stack.** -/
theorem hasRankThreePolynomialTerminalCertificate_of_singular_singletonSmithFiber
    [IsAlgClosed K]
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (hb : 0 < e.b) (hc : 0 < e.c) (hd : 0 < e.d)
    (hdeparture :
      HasFirstExactSmithExponentLongitudinalDeparture F e)
    (hsingular :
      HC4.Polynomial.hessianDeterminant
        (smithSubfacePolynomial (1 : Fin 4) 2 3 {e} F) = 0) :
    HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
      (phi := longitudinalCoefficientPolynomial e.b e.c e.d F)
      (e.b : K) (e.c : K) (e.d : K) 1 0 0 0 := by
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
  have hconst : phi.coeff 0 ≠ 0 :=
    rankThreeVertical_coeff_zero_ne_zero_of_hessianDeterminant_zero
      hb hc hd hphi hvertical
  exact
    HC4.RationalRigidity.hasRankThreePolynomialTerminalCertificate_of_vertical_line
      hb hc hd hdeg hconst hvertical

end

end HC4.Valuation
