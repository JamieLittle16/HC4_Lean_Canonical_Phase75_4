import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberRoot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberThreeLayerReflection
import HC4.Valuation.RankThreeLineSpecialisationHessianDeterminantSwap
import HC4.Polynomial.FiniteStaircaseEndpointDoubleRootEvaluation
import HC4.Polynomial.FiniteStaircaseThreeLayerIntermediateEvaluation
import HC4.Polynomial.FiniteStaircaseEndpointCrossScaled
import Mathlib.Tactic

/-!
# A19 middle unit one-fibre diagonal is impossible

On `j+1=k`, write `q_hi=n-k`, `q_lo=k-1`, `N=n-1`.  The unit wall equation
and endpoint separation force `q_hi < q_lo`, hence `q_lo < N < 2 q_lo`.
The order-`N` coefficient of the reflected determinant is therefore the direct
locked/highest cross first variation.  Evaluating at twice their common affine
root makes that coefficient a manifestly nonzero product.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrPairReesData

/-- Middle unit one-fibre contradiction. -/
theorem unitLeft_oneFiber_middle_diagonal_impossible
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 1 = Alo.k) : False := by
  let a0 : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b0 : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  let c0 : K := MvPolynomial.coeff F.highest.e0 S.slice
  let d0 : K := MvPolynomial.coeff F.highest.e1 S.slice
  let cLo : K := a0 * ((F.locked.ell : K) + 1)
  let dLo : K := b0 * (F.locked.ell : K)
  let cHi : K := c0 * (F.highest.n : K)
  let dHi : K := d0 * ((F.highest.n - 1 : ℕ) : K)
  let alpha : K := -cLo / dLo
  let lamHi : K := d0 * alpha / (F.highest.n : K)
  let lamLo : K := b0 * alpha / ((F.locked.ell : K) + 1)

  have ha0 : a0 ≠ 0 := by
    dsimp [a0]
    exact F.locked.facet_provenance.carrier_coeff_ne
  have hb0 : b0 ≠ 0 := by
    dsimp [b0]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hc0 : c0 ≠ 0 := by
    dsimp [c0]
    apply MvPolynomial.mem_support_iff.mp
    rw [F.highest.slice_support_eq]
    simp
  have hd0 : d0 ≠ 0 := by
    dsimp [d0]
    apply MvPolynomial.mem_support_iff.mp
    rw [F.highest.slice_support_eq]
    simp
  have hellK : (F.locked.ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt F.locked.ell_pos)
  have hell1K : (F.locked.ell : K) + 1 ≠ 0 := by
    have h : F.locked.ell + 1 ≠ 0 := by omega
    exact_mod_cast h
  have hnK : (F.highest.n : K) ≠ 0 := by
    exact_mod_cast (show F.highest.n ≠ 0 by omega)
  have hn1K : (F.highest.n : K) - 1 ≠ 0 := by
    have h : ((F.highest.n - 1 : ℕ) : K) ≠ 0 := by
      exact_mod_cast (show F.highest.n - 1 ≠ 0 by omega)
    simpa [Nat.cast_sub (by omega : 1 ≤ F.highest.n)] using h
  have hcLo : cLo ≠ 0 := by
    dsimp [cLo]
    exact mul_ne_zero ha0 hell1K
  have hdLo : dLo ≠ 0 := by
    dsimp [dLo]
    exact mul_ne_zero hb0 hellK
  have hdHi : dHi ≠ 0 := by
    dsimp [dHi]
    have hn1Cast : ((F.highest.n - 1 : ℕ) : K) ≠ 0 := by
      exact_mod_cast (show F.highest.n - 1 ≠ 0 by omega)
    exact mul_ne_zero hd0 hn1Cast
  have halpha : alpha ≠ 0 := by
    dsimp [alpha]
    exact div_ne_zero (neg_ne_zero.mpr hcLo) hdLo

  have hrootLo :
      a0 * ((F.locked.ell : K) + 1) +
        b0 * (F.locked.ell : K) * alpha = 0 := by
    change cLo + dLo * alpha = 0
    dsimp [alpha]
    field_simp [hdLo]
    ring
  have hrootEq := F.oneFiber_endpointRoots_eq
    Alo Ahi hthree houtThree hext
  have halphaHi : alpha = -cHi / dHi := by
    simpa [a0, b0, c0, d0, cLo, dLo, cHi, dHi, alpha] using hrootEq
  have hrootHi :
      c0 * (F.highest.n : K) +
        d0 * ((F.highest.n - 1 : ℕ) : K) * alpha = 0 := by
    change cHi + dHi * alpha = 0
    rw [halphaHi]
    field_simp [hdHi]
    ring
  have hlamHi : lamHi ≠ 0 := by
    dsimp [lamHi]
    exact div_ne_zero (mul_ne_zero hd0 halpha) hnK
  have hlamLo : lamLo ≠ 0 := by
    dsimp [lamLo]
    exact div_ne_zero (mul_ne_zero hb0 halpha) hell1K

  have hwall := Alo.wallSlope_eq hthree houtThree
  have hnell : F.highest.n ≤ F.locked.ell := by
    have hsep := F.highest_n_lt_locked_height hthree houtThree
    omega
  have hwallNat :
      (F.highest.n - 1) * (Alo.k - 1) =
        F.locked.ell * (F.highest.n - Alo.k) := by
    have hraw :
        (F.highest.n - 1) * Alo.j =
          F.locked.ell * (F.highest.n - Alo.k) := by
      exact_mod_cast hwall
    have hj : Alo.j = Alo.k - 1 := by omega
    simpa [hj] using hraw
  have hgapLt : F.highest.n - Alo.k < Alo.k - 1 := by
    by_contra hnotlt
    have hle : Alo.k - 1 ≤ F.highest.n - Alo.k :=
      Nat.le_of_not_gt hnotlt
    have h1 :
        (F.highest.n - 1) * (Alo.k - 1) ≤
          (F.highest.n - 1) * (F.highest.n - Alo.k) :=
      Nat.mul_le_mul_left _ hle
    have h2 :
        (F.highest.n - 1) * (F.highest.n - Alo.k) <
          F.highest.n * (F.highest.n - Alo.k) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have h3 :
        F.highest.n * (F.highest.n - Alo.k) ≤
          F.locked.ell * (F.highest.n - Alo.k) :=
      Nat.mul_le_mul_right _ hnell
    have hbad :
        F.locked.ell * (F.highest.n - Alo.k) <
          F.locked.ell * (F.highest.n - Alo.k) := by
      calc
        F.locked.ell * (F.highest.n - Alo.k) =
            (F.highest.n - 1) * (Alo.k - 1) := hwallNat.symm
        _ ≤ (F.highest.n - 1) * (F.highest.n - Alo.k) := h1
        _ < F.highest.n * (F.highest.n - Alo.k) := h2
        _ ≤ F.locked.ell * (F.highest.n - Alo.k) := h3
    exact (Nat.lt_irrefl _ hbad)

  let AloM := lockedBinomialMomentHessian 1 F.locked.ell a0 b0
  let Bmid := parallelStaircaseMomentHessian 1 Alo.k Alo.j Alo.coefficientProfile
  let AhiM := highestBinomialMomentHessian 1 F.highest.n c0 d0
  let qLo := Alo.k - 1
  let N := F.highest.n - 1
  let x := 2 * alpha

  have hqLo : 0 < qLo := by dsimp [qLo]; omega
  have hqLoN : qLo < N := by dsimp [qLo, N]; omega
  have hN2qLo : N < 2 * qLo := by
    dsimp [qLo, N]
    omega

  have hdetRefl :
      (parameterThreeLayerMatrix AloM Bmid AhiM qLo N).det = 0 := by
    have hp := D.det_unitLeftOneFiberReflectedThreeLayerMomentPencil_eq_zero
      F Alo Ahi hthree houtThree hnot hext
    simpa [AhiM, Bmid, AloM, qLo, N,
      unitLeftOneFiberReflectedThreeLayerMomentPencil, parameterThreeLayerMatrix,
      c0, d0, a0, b0] using hp

  have hcrossZero := snd_det_endpointDualPencil_eval_eq_zero
    x AloM Bmid AhiM qLo N hqLo hqLoN hN2qLo hdetRefl

  have hEvalLo : evalPolynomialMatrix x AloM =
      lamLo • lockedDoubleRootMomentCore (1 : K) (F.locked.ell : K) := by
    dsimp [x, AloM]
    exact eval_two_mul_lockedBinomialMomentHessian_of_root
      1 F.locked.ell a0 b0 alpha F.locked.ell_pos hrootLo
  have hEvalHi : evalPolynomialMatrix x AhiM =
      lamHi • highestDoubleRootMomentCore (1 : K) (F.highest.n : K) := by
    dsimp [x, AhiM]
    exact eval_two_mul_highestBinomialMomentHessian_of_root
      1 F.highest.n c0 d0 alpha (by omega) hrootHi
  rw [hEvalLo, hEvalHi,
    snd_det_endpointDualPencil_scaled_lockedHighest] at hcrossZero

  have h4 : (4 : K) ≠ 0 := by norm_num
  have hV : (1 : K) ≠ 0 := by norm_num
  have hV1 : (1 : K) + 1 ≠ 0 := by norm_num
  have hfactor :
      4 * (1 : K) * ((1 : K) + 1) *
          (F.locked.ell : K) ^ 3 * (F.highest.n : K) *
          ((F.locked.ell : K) + 1) ^ 3 *
          ((F.highest.n : K) - 1) ^ 2 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero h4 hV) hV1)
              (pow_ne_zero 3 hellK))
            hnK)
          (pow_ne_zero 3 hell1K))
      (pow_ne_zero 2 hn1K)
  have hscale : lamLo ^ 3 * lamHi ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hlamLo) hlamHi
  exact (mul_ne_zero hscale hfactor) hcrossZero

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
