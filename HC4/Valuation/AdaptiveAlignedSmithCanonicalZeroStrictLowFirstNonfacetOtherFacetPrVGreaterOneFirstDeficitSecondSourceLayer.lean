import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFirstDeficitSecondInteraction
import HC4.Newton.TerminalTwoZeroSupport
import Mathlib.Tactic

/-!
# Honest source layer forced by the second staggered interaction

The second-interaction theorem is a statement about one diagonal coefficient
of the complete total-deficit Hessian series.  This file converts that
coefficient back to literal source support.

If the missing diagonal is nonzero at parameter order

    k = 2*j - q,

then the exact parameter layer at order `k` has a nonzero second derivative
in the missing source coordinate.  Therefore an actual monomial of that layer
uses the missing coordinate with exponent at least two.  Since the
total-deficit Rees family has exact source-layer provenance, the monomial lies
in the original planar carrier and has total deficit exactly `k`.

No reflected-deficit formula is asserted here.  In particular, the missing
exponent is only proved to be at least two; proving that it is exactly two is
a separate finite-staircase step.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero pure second derivative must come from an actual source monomial
using the differentiated coordinate at least twice. -/
theorem exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
    (i : Fin 4)
    (Q : MvPolynomial (Fin 4) K)
    (hsecond :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) ≠ 0) :
    ∃ d ∈ Q.support, 2 ≤ d i := by
  by_contra hnone
  push_neg at hnone
  have hfirstSupport :
      ∀ m : Fin 4 →₀ ℕ,
        MvPolynomial.coeff m (MvPolynomial.pderiv i Q) ≠ 0 →
          m i = 0 := by
    intro m hm
    rw [coeff_pderiv_backport] at hm
    let d : Fin 4 →₀ ℕ := m + Finsupp.single i 1
    have hdcoeff : MvPolynomial.coeff d Q ≠ 0 := by
      intro hz
      dsimp [d] at hz
      rw [hz, zero_mul] at hm
      exact hm rfl
    have hdmem : d ∈ Q.support :=
      MvPolynomial.mem_support_iff.mpr hdcoeff
    have hdlt : d i < 2 := hnone d hdmem
    have hdi : d i = m i + 1 := by
      simp [d]
    omega
  have hzero :
      MvPolynomial.pderiv i (MvPolynomial.pderiv i Q) = 0 := by
    exact pderiv_eq_zero_of_all_supported_exponents_zero
      i (MvPolynomial.pderiv i Q) hfirstSupport
  exact hsecond hzero

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

/-- The left staggered missing diagonal is literally the `(2,2)` Hessian
entry of the exact total-deficit source layer. -/
theorem firstDeficitLeftStaggeredBlock_z_coeff
    (n : ℕ) :
    G.firstDeficitLeftStaggeredBlock.z.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (2 : Fin 4) 2 := by
  unfold firstDeficitLeftStaggeredBlock
    firstDeficitLeftStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitLeftStaggeredPerm]
  rw [parameterFirstHessian_coeff]
  simp [-standardTwoZero_pderiv_two_eq_A,
    HC4.Polynomial.hessian_apply, standardTwoZeroA]

/-- Right-oriented mirror: the missing diagonal is the `(1,1)` Hessian
entry of the exact source layer. -/
theorem firstDeficitRightStaggeredBlock_z_coeff
    (n : ℕ) :
    G.firstDeficitRightStaggeredBlock.z.coeff n =
      HC4.Polynomial.hessian
        (familyParameterLayer P.centralDeficitFamily n)
        (1 : Fin 4) 1 := by
  unfold firstDeficitRightStaggeredBlock
    firstDeficitRightStaggeredMatrix
    GeneralFourBlock.ofSymmetricMatrix
  simp only [Matrix.submatrix_apply]
  simp [firstDeficitRightStaggeredPerm]
  rw [parameterFirstHessian_coeff]
  simpa [HC4.Polynomial.hessian_apply]

/-- Provenance-rich source monomial forced at the second interaction order. -/
inductive FirstDeficitSecondSourceLayerGeometry : Prop
  | left
      (first opposite second : Fin 4 →₀ ℕ)
      (q j k : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (j_eq : j = opposite 1 + opposite 2)
      (k_eq : k = 2 * j - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = q)
      (first_two : first 2 = 0)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_two : opposite 2 = 1)
      (q_lt_j : q < j)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = k)
      (second_two_ge : 2 ≤ second 2)
  | right
      (first opposite second : Fin 4 →₀ ℕ)
      (q j k : ℕ)
      (q_eq : q = G.firstDeficitOrder)
      (j_eq : j = opposite 1 + opposite 2)
      (k_eq : k = 2 * j - q)
      (first_mem : first ∈ G.firstDeficitLayer.support)
      (first_one : first 1 = 0)
      (first_two : first 2 = q)
      (opposite_mem : opposite ∈ P.carrier.support)
      (opposite_one : opposite 1 = 1)
      (q_lt_j : q < j)
      (second_mem : second ∈ P.carrier.support)
      (second_order : second 1 + second 2 = k)
      (second_one_ge : 2 ≤ second 1)

/-- **Second interaction -> honest source layer.**

The forced diagonal coefficient at `2*j-q` is realized by an actual source
monomial in precisely that total-deficit layer, with missing-coordinate
exponent at least two. -/
theorem firstDeficit_secondSourceLayerGeometry
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    G.FirstDeficitSecondSourceLayerGeometry := by
  rcases G.firstDeficit_secondInteractionGeometry hthree houtThree with O
  cases O with
  | left first opposite B hfirst hfirst1 hfirst2 huniq hop hop2
      hstrict hminimal hB hlayer hmixed hz =>
      let q := G.firstDeficitOrder
      let j := opposite 1 + opposite 2
      let k := 2 * j - q
      have hderiv :
          MvPolynomial.pderiv (2 : Fin 4)
            (MvPolynomial.pderiv (2 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily k)) ≠ 0 := by
        have hz' := hz
        change G.firstDeficitLeftStaggeredBlock.z.coeff k ≠ 0 at hz'
        rw [G.firstDeficitLeftStaggeredBlock_z_coeff k] at hz'
        simpa [HC4.Polynomial.hessian_apply] using hz'
      rcases exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
          (K := K) (2 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily k) hderiv with
        ⟨second, hsecondLayer, hsecond2⟩
      have hsource :=
        (P.centralDeficitFamily_layer_mem_iff k second).1 hsecondLayer
      exact .left first opposite second q j k
        rfl rfl rfl hfirst
        (by simpa [q] using hfirst1) hfirst2
        hop hop2 (by simpa [q, j] using hstrict)
        hsource.1 hsource.2 hsecond2
  | right first opposite B hfirst hfirst1 hfirst2 huniq hop hop1
      hstrict hminimal hB hlayer hmixed hz =>
      let q := G.firstDeficitOrder
      let j := opposite 1 + opposite 2
      let k := 2 * j - q
      have hderiv :
          MvPolynomial.pderiv (1 : Fin 4)
            (MvPolynomial.pderiv (1 : Fin 4)
              (familyParameterLayer P.centralDeficitFamily k)) ≠ 0 := by
        have hz' := hz
        change G.firstDeficitRightStaggeredBlock.z.coeff k ≠ 0 at hz'
        rw [G.firstDeficitRightStaggeredBlock_z_coeff k] at hz'
        simpa [HC4.Polynomial.hessian_apply] using hz'
      rcases exists_support_exponent_ge_two_of_pderiv_pderiv_ne_zero
          (K := K) (1 : Fin 4)
          (familyParameterLayer P.centralDeficitFamily k) hderiv with
        ⟨second, hsecondLayer, hsecond1⟩
      have hsource :=
        (P.centralDeficitFamily_layer_mem_iff k second).1 hsecondLayer
      exact .right first opposite second q j k
        rfl rfl rfl hfirst hfirst1
        (by simpa [q] using hfirst2)
        hop hop1 (by simpa [q, j] using hstrict)
        hsource.1 hsource.2 hsecond1

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
