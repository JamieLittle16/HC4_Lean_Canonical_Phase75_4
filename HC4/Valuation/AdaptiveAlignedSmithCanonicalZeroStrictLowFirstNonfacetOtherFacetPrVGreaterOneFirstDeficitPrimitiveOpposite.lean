import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitStaggeredBreak
import HC4.Valuation.AdaptiveAlignedSmithCanonicalKernelFirstContactTermination
import Mathlib.Tactic

/-!
# The least opposite first-deficit opening is primitive

The staggered first-kernel-break certificate has one especially strong
source-level consequence.  At the least later order which opens the missing
central-deficit coordinate, the kernel diagonal coefficient is forced to
vanish.  On the exact total-deficit source layer this is precisely the second
partial derivative in the missing coordinate.

The selected opposite source monomial has positive exponent in that
coordinate.  In characteristic zero, exponent at least two would force that
second derivative to be nonzero.  Therefore the selected missing exponent is
exactly one.

This result retains the original source monomials and their minimality
properties.  It does not turn the later rank-two coefficient minor into a
repair step.
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

/-- Source-honest opposite-opening package strengthened by the fact that the
newly opened coordinate occurs to exponent exactly one. -/
inductive FirstDeficitPrimitiveOppositeOpening : Type u
  | left
      (first opposite : Fin 4 →₀ ℕ)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = G.firstDeficitOrder)
      (first_two : first 2 = 0)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two_one : opposite 2 = 1)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 2 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)
  | right
      (first opposite : Fin 4 →₀ ℕ)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = G.firstDeficitOrder)
      (first_unique : ∀ f ∈ G.firstDeficitLayer.support, f = first)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one_one : opposite 1 = 1)
      (order_strict :
        G.firstDeficitOrder < opposite 1 + opposite 2)
      (minimal :
        ∀ f ∈ P.carrier.support, 0 < f 1 →
          opposite 1 + opposite 2 ≤ f 1 + f 2)

private theorem left_opposite_two_eq_one
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = G.firstDeficitOrder)
    (hfirst2 : first 2 = 0)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop2 : 0 < opposite 2)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 2 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    opposite 2 = 1 := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  let E : StaggeredSingularFirstKernelBreakFourBlockData
      (MvPolynomial (Fin 4) K) := {
    block := G.firstDeficitLeftStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitLeftStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := by
      rw [G.firstDeficitLeftStaggeredBlock_activeThree_eq]
      exact G.firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
        hthree houtThree hfirst hfirst1 hfirst2 huniq
    q_lower_zero := by
      intro n hn
      exact G.leftBlock_q_coeff_eq_zero_before hminimal hn
    s_lower_zero := by
      intro n hn
      exact G.leftBlock_s_coeff_eq_zero_before hminimal hn
    y_lower_zero := by
      intro n hn
      exact G.leftBlock_y_coeff_eq_zero_before hminimal hn
    z_lower_zero := by
      intro n hn
      exact G.leftBlock_z_coeff_eq_zero_before hminimal hn
    determinantCore_eq_zero :=
      G.firstDeficitLeftStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitLeftStaggeredBlock_kernel_break
        hop hop2 hstrict hfirstTwo
  }
  have hz := E.kernelDiagonal_coeff_kernelOrder_eq_zero
  have hdiag :
      (parameterFirstHessian P.centralDeficitFamily
        (2 : Fin 4) 2).coeff (opposite 1 + opposite 2) = 0 := by
    simpa [E, firstDeficitLeftStaggeredBlock,
      firstDeficitLeftStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hz
  rw [parameterFirstHessian_coeff] at hdiag
  have hopLayer :
      opposite ∈
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2)).support := by
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hop, rfl⟩
  by_contra hne
  have htwo : 2 ≤ opposite 2 := by omega
  have hsecond :
      MvPolynomial.pderiv (2 : Fin 4)
          (MvPolynomial.pderiv (2 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily
              (opposite 1 + opposite 2))) ≠ 0 :=
    pderiv_pderiv_ne_zero_of_support_exponent_ge_two
      (K := K) (2 : Fin 4)
      (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2))
      opposite hopLayer htwo
  exact hsecond (by
    simpa [HC4.Polynomial.hessian_apply] using hdiag)

private theorem right_opposite_one_eq_one
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {first opposite : Fin 4 →₀ ℕ}
    (hfirst : first ∈ G.firstDeficitLayer.support)
    (hfirst1 : first 1 = 0)
    (hfirst2 : first 2 = G.firstDeficitOrder)
    (huniq : ∀ f ∈ G.firstDeficitLayer.support, f = first)
    (hop : opposite ∈ P.carrier.support)
    (hop1 : 0 < opposite 1)
    (hstrict : G.firstDeficitOrder < opposite 1 + opposite 2)
    (hminimal :
      ∀ f ∈ P.carrier.support, 0 < f 1 →
        opposite 1 + opposite 2 ≤ f 1 + f 2) :
    opposite 1 = 1 := by
  have hfirstTwo : 2 ≤ G.firstDeficitOrder :=
    firstDeficitOrder_two_le G hthree houtThree
  let E : StaggeredSingularFirstKernelBreakFourBlockData
      (MvPolynomial (Fin 4) K) := {
    block := G.firstDeficitRightStaggeredBlock
    activeOrder := G.firstDeficitOrder
    kernelOrder := opposite 1 + opposite 2
    activeOrder_pos := G.firstDeficitOrder_pos
    active_lt_kernel := hstrict
    active_lower_zero :=
      G.firstDeficitRightStaggeredBlock_active_lower_zero hthree houtThree
    active_coeff_ne_zero := by
      rw [G.firstDeficitRightStaggeredBlock_activeThree_eq]
      exact G.firstDeficitRightActiveHessian_det_coeff_first_ne_zero
        hthree houtThree hfirst hfirst1 hfirst2 huniq
    q_lower_zero := by
      intro n hn
      exact G.rightBlock_q_coeff_eq_zero_before hminimal hn
    s_lower_zero := by
      intro n hn
      exact G.rightBlock_s_coeff_eq_zero_before hminimal hn
    y_lower_zero := by
      intro n hn
      exact G.rightBlock_y_coeff_eq_zero_before hminimal hn
    z_lower_zero := by
      intro n hn
      exact G.rightBlock_z_coeff_eq_zero_before hminimal hn
    determinantCore_eq_zero :=
      G.firstDeficitRightStaggeredBlock_determinantCore_eq_zero
    kernel_break :=
      G.firstDeficitRightStaggeredBlock_kernel_break
        hop hop1 hstrict hfirstTwo
  }
  have hz := E.kernelDiagonal_coeff_kernelOrder_eq_zero
  have hdiag :
      (parameterFirstHessian P.centralDeficitFamily
        (1 : Fin 4) 1).coeff (opposite 1 + opposite 2) = 0 := by
    simpa [E, firstDeficitRightStaggeredBlock,
      firstDeficitRightStaggeredMatrix,
      GeneralFourBlock.ofSymmetricMatrix] using hz
  rw [parameterFirstHessian_coeff] at hdiag
  have hopLayer :
      opposite ∈
        (familyParameterLayer P.centralDeficitFamily
          (opposite 1 + opposite 2)).support := by
    rw [P.centralDeficitFamily_layer_mem_iff]
    exact ⟨hop, rfl⟩
  by_contra hne
  have hone : 2 ≤ opposite 1 := by omega
  have hsecond :
      MvPolynomial.pderiv (1 : Fin 4)
          (MvPolynomial.pderiv (1 : Fin 4)
            (familyParameterLayer P.centralDeficitFamily
              (opposite 1 + opposite 2))) ≠ 0 :=
    pderiv_pderiv_ne_zero_of_support_exponent_ge_two
      (K := K) (1 : Fin 4)
      (familyParameterLayer P.centralDeficitFamily
        (opposite 1 + opposite 2))
      opposite hopLayer hone
  exact hsecond (by
    simpa [HC4.Polynomial.hessian_apply] using hdiag)

/-- **Primitive opposite opening.**  The least later source point which opens
the missing first-deficit coordinate does so to exponent exactly one. -/
theorem firstDeficit_primitiveOppositeOpening
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty G.FirstDeficitPrimitiveOppositeOpening := by
  rcases G.firstDeficit_oppositeOpening hthree houtThree with ⟨O⟩
  cases O with
  | left first opposite hfirst hfirst1 hfirst2 huniq
      hop hop2 hstrict hminimal =>
      have hone := G.left_opposite_two_eq_one
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop hop2 hstrict hminimal
      exact ⟨.left first opposite hfirst hfirst1 hfirst2 huniq
        hop hone hstrict hminimal⟩
  | right first opposite hfirst hfirst1 hfirst2 huniq
      hop hop1 hstrict hminimal =>
      have hone := G.right_opposite_one_eq_one
        hthree houtThree hfirst hfirst1 hfirst2 huniq
        hop hop1 hstrict hminimal
      exact ⟨.right first opposite hfirst hfirst1 hfirst2 huniq
        hop hone hstrict hminimal⟩

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
