import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralFirstLayerHessian
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
      binaryDeficitExponent e = d := by
  classical
  have hsum :
      G.firstDeficitBinaryFace =
        ∑ e ∈ G.firstDeficitLayer.support,
          MvPolynomial.monomial (binaryDeficitExponent e)
            (MvPolynomial.coeff e G.firstDeficitLayer) := by
    unfold firstDeficitBinaryFace
    calc
      centralDeficitBinarySpecialisation (K := K) G.firstDeficitLayer =
          centralDeficitBinarySpecialisation (K := K)
            (∑ e ∈ G.firstDeficitLayer.support,
              MvPolynomial.monomial e
                (MvPolynomial.coeff e G.firstDeficitLayer)) := by
            rw [MvPolynomial.as_sum G.firstDeficitLayer]
      _ = _ := by
        simp only [map_sum, centralDeficitBinarySpecialisation_monomial_eq]
  have hdSum :
      d ∈
        (∑ e ∈ G.firstDeficitLayer.support,
          MvPolynomial.monomial (binaryDeficitExponent e)
            (MvPolynomial.coeff e G.firstDeficitLayer)).support := by
    rwa [← hsum]
  have hdUnion := MvPolynomial.support_sum hdSum
  rcases Finset.mem_biUnion.mp hdUnion with ⟨e, he, hde⟩
  have hc := MvPolynomial.mem_support_iff.mp hde
  rw [MvPolynomial.coeff_monomial] at hc
  split at hc
  · next hEq =>
      exact ⟨e, he, hEq.symm⟩
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
  apply F.no_adjacent_deficits hthree houtThree heCarrier hgCarrier
  · simpa using hf0.trans (by
      rw [← h1e, ← h1g])
  · simpa using hd1.trans (by
      rw [← h2g, ← h2e])

/-- Axis-support alternative for the first positive binary deficit face. -/
theorem firstDeficitBinaryFace_axis_support
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (∀ d ∈ G.firstDeficitBinaryFace.support, d 1 = 0) ∨
      (∀ d ∈ G.firstDeficitBinaryFace.support, d 0 = 0) := by
  let D := G.firstDeficitOrder
  have hDpos : 0 < D := G.firstDeficitOrder_pos
  by_cases hDtwo : 2 ≤ D
  · rcases binaryHomogeneous_eq_linearFormPow_of_hessianDet_zero
        G.firstDeficitBinaryFace D
        G.firstDeficitBinaryFace_isHomogeneous
        (G.firstDeficitBinaryFace_ne_zero hthree houtThree)
        hDtwo
        (G.firstDeficitBinaryFace_hessian_zero hthree houtThree) with
      ⟨a, c, hnormal⟩
    have ha : a ≠ 0 := by
      intro ha
      apply G.firstDeficitBinaryFace_ne_zero hthree houtThree
      rw [hnormal, ha]
      simp
    by_cases hc0 : c 0 = 0
    · right
      intro d hd
      have hdcoeff := MvPolynomial.mem_support_iff.mp hd
      rw [hnormal, gradientRatioLinearForm_finTwo_eq, hc0] at hdcoeff
      simp only [MvPolynomial.C_zero, zero_mul, zero_add] at hdcoeff
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
    · by_cases hc1 : c 1 = 0
      · left
        intro d hd
        have hdcoeff := MvPolynomial.mem_support_iff.mp hd
        rw [hnormal, gradientRatioLinearForm_finTwo_eq, hc1] at hdcoeff
        simp only [MvPolynomial.C_zero, zero_mul, add_zero] at hdcoeff
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
      · obtain ⟨m, hDm⟩ : ∃ m : ℕ, D = m + 1 := by
          exact ⟨D - 1, by omega⟩
        have hsupp :=
          pure_and_adjacent_mem_support_C_mul_linearPower
            (a := a) (c := c) (m := m) ha hc0 hc1
        rw [← hDm, ← hnormal] at hsupp
        exact False.elim
          (G.firstDeficitBinaryFace_no_adjacent hthree houtThree
            hsupp.2 hsupp.1
            (by
              simp [binaryPureZeroExponent,
                binaryAdjacentZeroOneExponent, Finsupp.single_apply])
            (by
              simp [binaryPureZeroExponent,
                binaryAdjacentZeroOneExponent, Finsupp.single_apply]))
  · have hDone : D = 1 := by omega
    rcases MvPolynomial.support_nonempty.mpr
        (G.firstDeficitBinaryFace_ne_zero hthree houtThree) with ⟨d, hd⟩
    have hdeg := G.firstDeficitBinaryFace_isHomogeneous hd
    have hdegSum : d.degree = d 0 + d 1 := by
      rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply,
        Finsupp.sum_fintype]
      · simp [Fin.sum_univ_two]
      · intro i
        simp
    rw [hDone] at hdeg
    rw [hdegSum] at hdeg
    rcases Nat.eq_zero_or_pos (d 1) with hd1zero | hd1pos
    · left
      intro f hf
      have hfdeg := G.firstDeficitBinaryFace_isHomogeneous hf
      have hfdegSum : f.degree = f 0 + f 1 := by
        rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply,
          Finsupp.sum_fintype]
        · simp [Fin.sum_univ_two]
        · intro i
          simp
      rw [hDone, hfdegSum] at hfdeg
      by_contra hf1
      have hf1pos : 0 < f 1 := Nat.pos_of_ne_zero hf1
      have hd0 : d 0 = 1 := by omega
      have hf0 : f 0 = 0 := by omega
      exact G.firstDeficitBinaryFace_no_adjacent hthree houtThree
        hf hd (by omega) (by omega)
    · right
      have hd0 : d 0 = 0 := by omega
      intro f hf
      have hfdeg := G.firstDeficitBinaryFace_isHomogeneous hf
      have hfdegSum : f.degree = f 0 + f 1 := by
        rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply,
          Finsupp.sum_fintype]
        · simp [Fin.sum_univ_two]
        · intro i
          simp
      rw [hDone, hfdegSum] at hfdeg
      by_contra hf0
      have hf0pos : 0 < f 0 := Nat.pos_of_ne_zero hf0
      have hd1 : d 1 = 1 := by omega
      have hf1 : f 1 = 0 := by omega
      exact G.firstDeficitBinaryFace_no_adjacent hthree houtThree
        hd hf (by omega) (by omega)

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
