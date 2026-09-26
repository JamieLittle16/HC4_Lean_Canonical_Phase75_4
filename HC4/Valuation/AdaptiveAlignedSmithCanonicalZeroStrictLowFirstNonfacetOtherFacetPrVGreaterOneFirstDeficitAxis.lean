import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralFirstLayerLinearPower
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneAdjacentDeficit
import HC4.Polynomial.BinaryLinearPowerAdjacentSupport
import Mathlib.Tactic

/-!
# The first positive total-deficit layer is an axis layer

The source-honest total-deficit Rees family has a nonzero first positive
binary face Q.  It is homogeneous of its exact deficit order and its binary
Hessian determinant vanishes.

For degree one, every support point is already one of the two axis monomials;
the staircase adjacent-deficit exclusion prevents both from occurring.

For degree at least two, binary Hesse rigidity gives Q = a L^D.  If both
coefficients of L were nonzero, the explicit pure and adjacent coefficients
U^D and U^(D-1)V would both occur.  They lift to honest source support points,
contradicting the staircase adjacent-deficit exclusion.  Thus L is an axis
linear form and the complete first layer lies on one coordinate roof.
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

/-- Every binary support exponent of the first deficit face lifts to an actual
support exponent of the first source layer. -/
theorem firstDeficitBinaryFace_support_lifts
    {d : Fin 2 →₀ ℕ}
    (hd : d ∈ G.firstDeficitBinaryFace.support) :
    ∃ e : Fin 4 →₀ ℕ,
      e ∈ G.firstDeficitLayer.support ∧
      HC4.Polynomial.binaryDeficitExponent e = d := by
  classical
  have hsum :
      G.firstDeficitBinaryFace =
        ∑ e ∈ G.firstDeficitLayer.support,
          MvPolynomial.monomial (HC4.Polynomial.binaryDeficitExponent e)
            (MvPolynomial.coeff e G.firstDeficitLayer) := by
    unfold firstDeficitBinaryFace
    have has := MvPolynomial.as_sum G.firstDeficitLayer
    calc
      HC4.Polynomial.centralDeficitBinarySpecialisation (K := K) G.firstDeficitLayer =
          HC4.Polynomial.centralDeficitBinarySpecialisation (K := K)
            (∑ e ∈ G.firstDeficitLayer.support,
              MvPolynomial.monomial e
                (MvPolynomial.coeff e G.firstDeficitLayer)) := by
            exact congrArg
              (HC4.Polynomial.centralDeficitBinarySpecialisation (K := K)) has
      _ = _ := by
        simp only [map_sum, HC4.Polynomial.centralDeficitBinarySpecialisation_monomial_eq]
  have hdSum :
      d ∈
        (∑ e ∈ G.firstDeficitLayer.support,
          MvPolynomial.monomial (HC4.Polynomial.binaryDeficitExponent e)
            (MvPolynomial.coeff e G.firstDeficitLayer)).support := by
    rwa [← hsum]
  have hdUnion := MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨e, he, hde⟩
  have hc := MvPolynomial.mem_support_iff.mp hde
  rw [MvPolynomial.coeff_monomial] at hc
  split at hc
  · next hEq =>
      exact ⟨e, he, hEq⟩
  · exact (hc rfl).elim

/-- Adjacent binary deficit exponents cannot both occur in the first face. -/
theorem firstDeficitBinaryFace_no_adjacent
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {d f : Fin 2 →₀ ℕ}
    (hd : d ∈ G.firstDeficitBinaryFace.support)
    (hf : f ∈ G.firstDeficitBinaryFace.support)
    (hf0 : f 0 = d 0 + 1)
    (hd1 : d 1 = f 1 + 1) :
    False := by
  rcases G.firstDeficitBinaryFace_support_lifts hd with
    ⟨e, he, heq⟩
  rcases G.firstDeficitBinaryFace_support_lifts hf with
    ⟨g, hg, hgeq⟩
  have heCarrier := (G.firstDeficitLayer_support he).1
  have hgCarrier := (G.firstDeficitLayer_support hg).1
  have h1e := congrArg (fun q : Fin 2 →₀ ℕ => q (0 : Fin 2)) heq
  have h2e := congrArg (fun q : Fin 2 →₀ ℕ => q (1 : Fin 2)) heq
  have h1g := congrArg (fun q : Fin 2 →₀ ℕ => q (0 : Fin 2)) hgeq
  have h2g := congrArg (fun q : Fin 2 →₀ ℕ => q (1 : Fin 2)) hgeq
  have h1e' : e 1 = d 0 := by simpa using h1e
  have h2e' : e 2 = d 1 := by simpa using h2e
  have h1g' : g 1 = f 0 := by simpa using h1g
  have h2g' : g 2 = f 1 := by simpa using h2g
  apply F.no_adjacent_deficits hthree houtThree heCarrier hgCarrier
  · omega
  · omega

/-- Axis-support alternative for the first positive binary deficit face.

The nonlinear degree bound is already proved in
`CentralFirstLayerLinearPower`, so we consume its exact pure-axis normal form
rather than re-running the binary Hesse split here. -/
theorem firstDeficitBinaryFace_axis_support
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∀ d ∈ G.firstDeficitBinaryFace.support, d 1 = 0) ∨
      (∀ d ∈ G.firstDeficitBinaryFace.support, d 0 = 0) := by
  rcases firstDeficitBinaryFace_pureAxis G hthree houtThree with
    ⟨a, c, hnormal, _ha, haxis⟩
  let D := G.firstDeficitOrder
  rcases haxis with hzeroOne | hzeroZero
  · left
    intro d hd
    have hdcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [hnormal, HC4.Polynomial.gradientRatioLinearForm_finTwo_eq,
      hzeroOne.2] at hdcoeff
    simp only [map_zero, zero_mul, add_zero] at hdcoeff
    rw [MvPolynomial.coeff_C_mul] at hdcoeff
    by_contra hd1
    have hneq :
        Finsupp.single (0 : Fin 2) D ≠ d := by
      intro h
      have h1 := congrArg (fun q : Fin 2 →₀ ℕ => q (1 : Fin 2)) h
      simp [Finsupp.single_apply] at h1
      exact hd1 h1.symm
    have hpow :
        (MvPolynomial.C (c 0) * MvPolynomial.X (0 : Fin 2)) ^ D =
          MvPolynomial.C ((c 0) ^ D) *
            MvPolynomial.X (0 : Fin 2) ^ D := by
      rw [mul_pow, map_pow]
    rw [hpow, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X_pow, if_neg hneq] at hdcoeff
    simp at hdcoeff
  · right
    intro d hd
    have hdcoeff := MvPolynomial.mem_support_iff.mp hd
    rw [hnormal, HC4.Polynomial.gradientRatioLinearForm_finTwo_eq,
      hzeroZero.1] at hdcoeff
    simp only [map_zero, zero_mul, zero_add] at hdcoeff
    rw [MvPolynomial.coeff_C_mul] at hdcoeff
    by_contra hd0
    have hneq :
        Finsupp.single (1 : Fin 2) D ≠ d := by
      intro h
      have h0 := congrArg (fun q : Fin 2 →₀ ℕ => q (0 : Fin 2)) h
      simp [Finsupp.single_apply] at h0
      exact hd0 h0.symm
    have hpow :
        (MvPolynomial.C (c 1) * MvPolynomial.X (1 : Fin 2)) ^ D =
          MvPolynomial.C ((c 1) ^ D) *
            MvPolynomial.X (1 : Fin 2) ^ D := by
      rw [mul_pow, map_pow]
    rw [hpow, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X_pow, if_neg hneq] at hdcoeff
    simp at hdcoeff

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
