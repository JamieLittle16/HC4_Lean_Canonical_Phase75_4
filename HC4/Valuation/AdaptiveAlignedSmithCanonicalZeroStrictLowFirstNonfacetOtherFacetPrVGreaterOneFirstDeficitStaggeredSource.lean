import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitStaggeredBlock
import HC4.Polynomial.NonlinearSupportHessianRowBreak
import Mathlib.Tactic

/-!
# Source row for the staggered first-deficit kernel break

The opposite-opening selector retains the *least* total-deficit carrier
monomial which uses the still-missing central coordinate.  This file converts
that source statement into the exact Hessian-row facts needed by
`StaggeredSingularFirstKernelBreakFourBlockData`.

If the opposite opening occurs at order `j` in source coordinate `k`, then

* every parameter layer below `j` is independent of `x_k`, hence every
  entry in Hessian row `k` vanishes below `j`;
* the selected opposite monomial makes `∂_k` of layer `j` nonzero;
* because the first deficit order is at least two and `j` is strictly later,
  every monomial in layer `j` has ordinary degree at least three;
* the characteristic-zero nonlinear row-break lemma therefore produces an
  actual nonzero Hessian entry in row `k` at order `j`.

Everything is stated on the complete source-honest total-deficit Rees family.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- Minimality of an opposite opening makes every earlier exact source layer
independent of the missing coordinate. -/
theorem missingPderiv_firstDeficitLayer_eq_zero_of_lt
    (missing : Fin 4) (j : ℕ)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f missing →
        j ≤ f 1 + f 2)
    {n : ℕ} (hn : n < j) :
    MvPolynomial.pderiv missing
      (familyParameterLayer P.centralDeficitFamily n) = 0 := by
  apply HC4.Newton.pderiv_eq_zero_of_all_supported_exponents_zero
  intro d hdcoeff
  have hd :
      d ∈ (familyParameterLayer P.centralDeficitFamily n).support :=
    MvPolynomial.mem_support_iff.mpr hdcoeff
  have hsource :=
    (P.centralDeficitFamily_layer_mem_iff n d).1 hd
  by_cases hpos : 0 < d missing
  · have hjle := hminimal d hsource.1 hpos
    omega
  · exact Nat.eq_zero_of_not_pos hpos

/-- Consequently every entry of the missing Hessian row vanishes below the
opposite-opening order. -/
theorem missingHessianRow_coeff_eq_zero_of_lt
    (missing : Fin 4) (j : ℕ)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f missing →
        j ≤ f 1 + f 2)
    {n : ℕ} (hn : n < j)
    (i : Fin 4) :
    (parameterFirstHessian P.centralDeficitFamily missing i).coeff n = 0 := by
  rw [parameterFirstHessian_coeff]
  have hpd :=
    missingPderiv_firstDeficitLayer_eq_zero_of_lt
      missing j hminimal hn
  simp [HC4.Polynomial.hessian_apply, hpd]

/-- The selected opposite source monomial makes the missing first derivative
of its exact parameter layer nonzero. -/
theorem missingPderiv_firstDeficitLayer_ne_zero_at
    (missing : Fin 4)
    {opposite : Fin 4 →₀ ℕ}
    (hop : opposite ∈ P.carrier.support)
    (hpos : 0 < opposite missing) :
    MvPolynomial.pderiv missing
      (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2)) ≠ 0 := by
  have hopLayer :
      opposite ∈
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2)).support := by
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hop, rfl⟩
  have hcoeff :
      MvPolynomial.coeff opposite
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hopLayer
  intro hzero
  have hz :=
    HC4.Newton.exponent_eq_zero_of_pderiv_eq_zero
      missing
      (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2))
      hzero opposite hcoeff
  omega

/-- Every monomial of an exact total-deficit layer of order at least three is
nonlinear in ordinary source degree. -/
theorem centralDeficitLayer_support_degree_ge_three
    (j : ℕ) (hj : 3 ≤ j) :
    ∀ d ∈ (familyParameterLayer P.centralDeficitFamily j).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d := by
  intro d hd
  have hsource :=
    (P.centralDeficitFamily_layer_mem_iff j d).1 hd
  simp [HC4.Polynomial.ordinaryDegree4] at *
  omega

/-- At a later opposite opening `j>q>=2`, some honest Hessian entry in the
missing row is nonzero at exact parameter order `j`. -/
theorem exists_missingHessianRow_coeff_ne_zero_at
    (missing : Fin 4)
    {opposite : Fin 4 →₀ ℕ}
    (hop : opposite ∈ P.carrier.support)
    (hpos : 0 < opposite missing)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hfirstTwo : 2 ≤ G.firstDeficitOrder) :
    ∃ i : Fin 4,
      (parameterFirstHessian P.centralDeficitFamily missing i).coeff
          (opposite 1 + opposite 2) ≠ 0 := by
  let j := opposite 1 + opposite 2
  have hj : 3 ≤ j := by
    dsimp [j]
    omega
  have hpd :
      MvPolynomial.pderiv missing
        (familyParameterLayer P.centralDeficitFamily j) ≠ 0 := by
    simpa [j] using
      missingPderiv_firstDeficitLayer_ne_zero_at
        missing hop hpos
  have hdegree :
      ∀ d ∈ (familyParameterLayer P.centralDeficitFamily j).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d :=
    centralDeficitLayer_support_degree_ge_three j hj
  rcases
      HC4.Polynomial.exists_hessian_entry_ne_zero_of_pderiv_ne_zero_of_support_degree_ge_three
        missing
        (familyParameterLayer P.centralDeficitFamily j)
        hdegree hpd with
    ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rw [parameterFirstHessian_coeff]
  simpa [HC4.Polynomial.hessian_apply, j] using hi

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
