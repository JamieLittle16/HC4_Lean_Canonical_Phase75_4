import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementPatternSplit
import Mathlib.Tactic

/-!
# Hessian structure of the nonlinear-confinement branch

If every source monomial of ordinary degree at least three lies on one
coordinate facet, then every Hessian entry in the omitted row/column is
constant.  This is a purely coefficientwise consequence of the support
condition: any nonconstant monomial of such a Hessian entry would lift to a
source monomial of degree at least three with positive omitted-coordinate
exponent, contradicting facet confinement.

This is the first direct algebraic reduction of the final
`nonlinearConfined` constructor.  No JC2 projection, auxiliary clock, or
repair claim is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero four-variable exponent has positive ordinary degree. -/
private theorem ordinaryDegree4_pos_of_ne_zero
    (m : Fin 4 →₀ ℕ)
    (hm : m ≠ 0) :
    0 < HC4.Polynomial.ordinaryDegree4 m := by
  by_contra hnot
  have hzero : HC4.Polynomial.ordinaryDegree4 m = 0 :=
    Nat.eq_zero_of_not_pos hnot
  apply hm
  apply Finsupp.ext
  intro i
  unfold HC4.Polynomial.ordinaryDegree4 at hzero
  fin_cases i <;> omega

/-- **Facet confinement makes the omitted Hessian row constant.**

Only degree-at-most-two source terms may involve the omitted coordinate.
After two derivatives, every omitted-row Hessian entry is therefore a scalar
polynomial. -/
theorem hessian_omitted_eq_C_of_nonlinearConfinement
    (F : MvPolynomial (Fin 4) K)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ F.support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d))
    (i : Fin 4) :
    HC4.Polynomial.hessian F
        (HC4.Polynomial.facetOmittedCoordinate facet) i =
      MvPolynomial.C
        (MvPolynomial.coeff 0
          (HC4.Polynomial.hessian F
            (HC4.Polynomial.facetOmittedCoordinate facet) i)) := by
  classical
  let j := HC4.Polynomial.facetOmittedCoordinate facet
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0
  · subst m
    simp [j]
  · have hmdeg : 0 < HC4.Polynomial.ordinaryDegree4 m :=
      ordinaryDegree4_pos_of_ne_zero m hm
    let n : Fin 4 →₀ ℕ :=
      (m + Finsupp.single i 1) + Finsupp.single j 1
    have hdeg : 3 ≤ HC4.Polynomial.ordinaryDegree4 n := by
      dsimp [n, j]
      cases facet <;> fin_cases i <;>
        simp [HC4.Polynomial.ordinaryDegree4,
          HC4.Polynomial.facetOmittedCoordinate,
          Finsupp.single_apply] <;> omega
    have hjpos : 0 < n j := by
      dsimp [n]
      simp [Finsupp.single_apply]
    have hsource : MvPolynomial.coeff n F = 0 := by
      by_contra hne
      have hnmem : n ∈ F.support :=
        MvPolynomial.mem_support_iff.mpr hne
      have hfacet := hconfined n hnmem hdeg
      have hjzero : n j = 0 := by
        dsimp [j]
        exact
          (HC4.Polynomial.onFacet_toToricExponent_iff facet n).1 hfacet
      exact (Nat.ne_of_gt hjpos) hjzero
    change
      MvPolynomial.coeff m
          (MvPolynomial.pderiv i
            (MvPolynomial.pderiv j F)) =
        MvPolynomial.coeff m
          (MvPolynomial.C
            (MvPolynomial.coeff 0
              (HC4.Polynomial.hessian F j i)))
    rw [coeff_pderiv_backport, coeff_pderiv_backport]
    dsimp [n] at hsource
    simp [hsource, hm]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The final `nonlinearConfined` source therefore has a constant Hessian
row in the coordinate omitted by the confinement facet. -/
theorem nonlinearConfined_hessianRow_constant
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hconfined :
      ∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d))
    (i : Fin 4) :
    HC4.Polynomial.hessian
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family)
        (HC4.Polynomial.facetOmittedCoordinate facet) i =
      MvPolynomial.C
        (MvPolynomial.coeff 0
          (HC4.Polynomial.hessian
            (polynomialFamilySpecialFiber
              T.terminal.blocker.presented.family)
            (HC4.Polynomial.facetOmittedCoordinate facet) i)) :=
  hessian_omitted_eq_C_of_nonlinearConfinement
    (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family)
    facet hconfined i

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
