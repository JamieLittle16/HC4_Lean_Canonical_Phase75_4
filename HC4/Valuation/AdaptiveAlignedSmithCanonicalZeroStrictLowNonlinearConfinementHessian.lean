import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowConfinementPatternSplit
import HC4.Newton.MixedDegreeAxisCollision
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
  have hdeg : Finsupp.degree m ≠ 0 := by
    intro hz
    exact hm ((Finsupp.degree_eq_zero_iff m).mp hz)
  rw [← finsuppDegree_eq_ordinaryDegree4 m]
  exact Nat.pos_of_ne_zero hdeg

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
      unfold HC4.Polynomial.ordinaryDegree4 at hmdeg ⊢
      cases facet <;> fin_cases i <;>
        simp [HC4.Polynomial.facetOmittedCoordinate,
          Finsupp.add_apply, Finsupp.single_apply] <;> omega
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
    have h0m : (0 : Fin 4 →₀ ℕ) ≠ m := by
      intro h
      exact hm h.symm
    simp [hsource, h0m]

/-- A constant Hessian coupling to the distinguished longitudinal coordinate
vanishes under the normalized axis collision `0 ↔ e₀`.

This is the one-variable fundamental-theorem-of-calculus calculation used in
the older direct-closing terminal, isolated here without any terminal-specific
geometry. -/
theorem hessian_longitudinal_constant_eq_zero_of_axisCollision
    (F : MvPolynomial (Fin 4) K)
    (j : Fin 4)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)))
    (c : K)
    (hconst :
      HC4.Polynomial.hessian F j (0 : Fin 4) =
        MvPolynomial.C c) :
    c = 0 := by
  let G : Polynomial K :=
    longitudinalAxisRestriction (MvPolynomial.pderiv j F)
  have hGderiv : G.derivative = Polynomial.C c := by
    dsimp [G]
    rw [← longitudinalAxisRestriction_pderiv_zero]
    rw [show
      MvPolynomial.pderiv (0 : Fin 4) (MvPolynomial.pderiv j F) =
          MvPolynomial.C c by
        simpa [HC4.Polynomial.hessian_apply] using hconst]
    simp [longitudinalAxisRestriction]
  have hgrad :
      Polynomial.eval (0 : K) G =
        Polynomial.eval (1 : K) G := by
    have h := hcoll j
    rw [eval_finCons_zero_eq_longitudinalAxisRestriction,
      eval_finCons_zero_eq_longitudinalAxisRestriction] at h
    simpa [G] using h
  let R : Polynomial K := G - Polynomial.C c * Polynomial.X
  have hRderiv : R.derivative = 0 := by
    dsimp [R]
    rw [Polynomial.derivative_sub, hGderiv,
      Polynomial.derivative_C_mul_X]
    simp
  have hRconst := Polynomial.eq_C_of_derivative_eq_zero hRderiv
  have heval :
      Polynomial.eval (0 : K) R =
        Polynomial.eval (1 : K) R := by
    rw [hRconst]
  have hcRelation :
      Polynomial.eval (0 : K) G =
        Polynomial.eval (1 : K) G - c := by
    simpa [R] using heval
  linear_combination hgrad - hcRelation

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
