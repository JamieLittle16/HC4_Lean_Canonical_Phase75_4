import HC4.Newton.MvBoundaryStrata
import HC4.Newton.InteriorVertex
import Mathlib.Tactic

/-!
# A18.5.20: exposed singular balanced vertices have only two boundary types

The two ingredients needed by the terminal Newton-edge argument are already
verified independently:

* `InteriorVertex` says a nonlinear singleton exposed from a zero-Hessian
  polynomial must omit a coordinate;
* `MvBoundaryStrata` says a balanced multivariate boundary exponent is either
  rank three in one facet or lies on an extreme transition ray.

This file composes them while retaining the actual exponent of the honest
`MvPolynomial`.  It is the endpoint classifier used before the rank-three and
complementary-edge obstructions.
-/

namespace HC4.Newton

open HC4.Polynomial
open HC4.Toric
open MvPolynomial

noncomputable section

/-- **Exposed balanced singular vertex dichotomy.** -/
theorem exposed_balanced_monomial_rankThree_or_extremeRay
    {K : Type*} [Field K] [CharZero K]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {F : MvPolynomial (Fin 4) K}
    (hBal : HasBalancedMvSupport a b F)
    {w : Fin 4 → ℤ} {level : ℤ}
    {d : Fin 4 →₀ ℕ} {c : K}
    (hbound : IsWeightLE w level F)
    (hzero : hessianDeterminant F = 0)
    (hinit : initialForm w level F = MvPolynomial.monomial d c)
    (hc : c ≠ 0)
    (hdeg : 3 ≤ ordinaryDegree4 d) :
    (∃ facet : ToricFacet, MvRankThreeOnFacet facet d) ∨
      (∃ facet next : ToricFacet,
        AdjacentFacets facet next ∧
          OnRay a b facet next (toToricExponent d)) := by
  have hbdry : MvExponentOnBoundary d :=
    exposed_monomial_on_boundary_of_zero_hessian
      hbound hzero hinit hc hdeg
  have hmemInitial : d ∈ (initialForm w level F).support := by
    rw [hinit]
    simp [MvPolynomial.mem_support_iff, hc]
  have hmemF : d ∈ F.support :=
    support_initialForm_subset w level F hmemInitial
  have hBalanced : IsBalancedExponent a b d := hBal d hmemF
  exact mvBoundary_rankThree_or_extremeRay ha hb hcop hBalanced hbdry

/-- In the longitudinal `qs` chart, the rank-three branch exposes precisely a
zero longitudinal exponent and three positive transverse exponents. -/
theorem exposed_balanced_monomial_qs_positive
    {K : Type*} [Field K] [CharZero K]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b)
    {F : MvPolynomial (Fin 4) K}
    (hBal : HasBalancedMvSupport a b F)
    {w : Fin 4 → ℤ} {level : ℤ}
    {d : Fin 4 →₀ ℕ} {c : K}
    (hbound : IsWeightLE w level F)
    (hzero : hessianDeterminant F = 0)
    (hinit : initialForm w level F = MvPolynomial.monomial d c)
    (hc : c ≠ 0)
    (hdeg : 3 ≤ ordinaryDegree4 d)
    (hqs : MvRankThreeOnFacet .qs d) :
    d 0 = 0 ∧ 0 < d 1 ∧ 0 < d 2 ∧ 0 < d 3 := by
  exact mvRankThreeOnFacet_qs hqs

end

end HC4.Newton
