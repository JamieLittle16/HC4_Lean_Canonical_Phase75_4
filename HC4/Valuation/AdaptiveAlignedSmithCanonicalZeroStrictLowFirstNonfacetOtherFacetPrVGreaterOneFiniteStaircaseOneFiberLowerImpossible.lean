import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberThreeLayerReflection
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberLeading
import HC4.Polynomial.FiniteStaircaseEndpointMomentDegree
import HC4.Polynomial.FiniteStaircasePureModeSecondVariation
import HC4.Polynomial.FiniteStaircaseThreeLayerSecondVariation
import Mathlib.Tactic

/-!
# A19 lower pure one-fibre diagonal is impossible

This is the reflected endpoint-dual of the upper one-fibre elimination.  On
`j+2=k`, the honest interior profile has degree exactly `k-1`.  Reflection of
the exact pair-Rees pencil gives

    H_locked + tau^(k-1) H_int + tau^(n-1) H_high.

The generic three-layer second-variation theorem shows that the top
longitudinal second variation of the locked/interior pair must vanish.  The
state-free pure-mode calculation makes it an explicit product of nonzero
factors, contradiction.
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

/-- **Lower one-fibre elimination.** -/
theorem oneFiber_lower_diagonal_impossible
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (D : QsOtherFacetPrPairReesData C P S F.highest.n)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F D)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnot : ¬ F.NoStrictInteriorSupport)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 2 = Alo.k) : False := by
  let a : K := MvPolynomial.coeff C.ray.facetExponent P.carrier
  let b : K := MvPolynomial.coeff C.ray.outsideExponent P.carrier
  let u : K := Alo.coefficientProfile.coeff (Alo.k - 1)
  let A := lockedBinomialMomentHessian F.V F.locked.ell a b
  let B := parallelStaircaseMomentHessian F.V Alo.k Alo.j Alo.coefficientProfile
  let Cend := highestBinomialMomentHessian F.V F.highest.n
    (MvPolynomial.coeff F.highest.e0 S.slice)
    (MvPolynomial.coeff F.highest.e1 S.slice)
  let q := Alo.k - 1
  let N := F.highest.n - 1

  have hqpos : 0 < q := by
    dsimp [q]
    omega
  have hqN : q < N := by
    dsimp [q, N]
    omega
  have hm : 1 < Alo.k - 1 := by
    omega

  have hrefDet := D.det_oneFiberReflectedThreeLayerMomentPencil_eq_zero
    F Alo Ahi hthree houtThree hnot hext
  have hdet :
      (parameterThreeLayerMatrix A B Cend q N).det = 0 := by
    simpa [A, B, Cend, q, N, parameterThreeLayerMatrix,
      oneFiberReflectedThreeLayerMomentPencil] using hrefDet

  have hAdeg : ∀ i j, (A i j).natDegree ≤ 1 := by
    intro i j
    dsimp [A, a, b]
    exact lockedBinomialMomentHessian_natDegree_le_one
      F.V F.locked.ell _ _ i j

  have hprofileDeg := F.oneFiber_lower_profile_natDegree_eq
    Alo Ahi hthree houtThree hext hdiag
  have hBdeg : ∀ i j, (B i j).natDegree ≤ Alo.k - 1 := by
    intro i j
    dsimp [B]
    calc
      (parallelStaircaseMomentHessian F.V Alo.k Alo.j
        Alo.coefficientProfile i j).natDegree ≤
          Alo.coefficientProfile.natDegree :=
        parallelStaircaseMomentHessian_natDegree_le
          F.V Alo.k Alo.j Alo.coefficientProfile i j
      _ = Alo.k - 1 := hprofileDeg

  have hCdeg : ∀ i j, (Cend i j).natDegree ≤ 1 := by
    intro i j
    dsimp [Cend]
    exact highestBinomialMomentHessian_natDegree_le_one
      F.V F.highest.n _ _ i j

  have htopZero :=
    snd_snd_det_secondVariationTopMatrix_eq_zero_of_threeLayer_det_zero
      A B Cend q N (Alo.k - 1) hqpos hqN hm hdet hAdeg hBdeg hCdeg

  have hAcoeff := coeff_one_lockedBinomialMomentHessian
    F.V F.locked.ell a b
  have hBcoeff := F.oneFiber_lower_moment_top_coeff Alo hdiag
  have hTopMatrix :
      secondVariationTopMatrix A B (Alo.k - 1) =
        lockedLowerPureModeSecondJet
          (F.V : K) (F.locked.ell : K) (Alo.k : K) b u := by
    apply Matrix.ext
    intro i j
    have hAi := congrFun (congrFun hAcoeff i) j
    have hBi := congrFun (congrFun hBcoeff i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hAi hBi
    have hk1 : (((Alo.k - 1 : ℕ) : K)) = (Alo.k : K) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ Alo.k by omega)]
      simp
    simp [secondVariationTopMatrix, secondVariationTopEntry,
      lockedLowerPureModeSecondJet, A, B, u, hk1]
    rw [hAi, hBi]

  rw [hTopMatrix] at htopZero
  rw [snd_snd_det_lockedLowerPureModeSecondJet] at htopZero

  have hb : b ≠ 0 := by
    dsimp [b]
    exact F.locked.outside_provenance.carrier_coeff_ne
  have hu : u ≠ 0 := by
    dsimp [u]
    exact F.oneFiber_lower_profile_top_ne_zero
      Alo Ahi hthree houtThree hext hdiag
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hV : (F.V : K) ≠ 0 := by
    exact_mod_cast (show F.V ≠ 0 by omega)
  have hV1 : (F.V : K) + 1 ≠ 0 := by
    have h : (F.V + 1 : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  have hell : (F.locked.ell : K) ≠ 0 := by
    exact_mod_cast (show F.locked.ell ≠ 0 by omega)
  have hell1 : (F.locked.ell : K) - 1 ≠ 0 := by
    intro hz
    have hz' : (F.locked.ell : K) = 1 := sub_eq_zero.mp hz
    have hn : F.locked.ell = 1 := by exact_mod_cast hz'
    omega
  have hk1 : (Alo.k : K) - 1 ≠ 0 := by
    intro hz
    have hz' : (Alo.k : K) = 1 := sub_eq_zero.mp hz
    have hn : Alo.k = 1 := by exact_mod_cast hz'
    omega

  have h0 : (2 : K) * (F.V : K) ≠ 0 := mul_ne_zero htwo hV
  have h1 : (2 : K) * (F.V : K) * ((F.V : K) + 1) ≠ 0 :=
    mul_ne_zero h0 hV1
  have h2 :
      (2 : K) * (F.V : K) * ((F.V : K) + 1) *
        (F.locked.ell : K) ^ 2 ≠ 0 :=
    mul_ne_zero h1 (pow_ne_zero 2 hell)
  have h3 :
      (2 : K) * (F.V : K) * ((F.V : K) + 1) *
        (F.locked.ell : K) ^ 2 * ((F.locked.ell : K) - 1) ≠ 0 :=
    mul_ne_zero h2 hell1
  have h4 :
      (2 : K) * (F.V : K) * ((F.V : K) + 1) *
        (F.locked.ell : K) ^ 2 * ((F.locked.ell : K) - 1) *
        ((Alo.k : K) - 1) ^ 2 ≠ 0 :=
    mul_ne_zero h3 (pow_ne_zero 2 hk1)
  have h5 :
      (2 : K) * (F.V : K) * ((F.V : K) + 1) *
        (F.locked.ell : K) ^ 2 * ((F.locked.ell : K) - 1) *
        ((Alo.k : K) - 1) ^ 2 * b ^ 2 ≠ 0 :=
    mul_ne_zero h4 (pow_ne_zero 2 hb)
  have h6 :
      (2 : K) * (F.V : K) * ((F.V : K) + 1) *
        (F.locked.ell : K) ^ 2 * ((F.locked.ell : K) - 1) *
        ((Alo.k : K) - 1) ^ 2 * b ^ 2 * u ^ 2 ≠ 0 :=
    mul_ne_zero h5 (pow_ne_zero 2 hu)
  exact h6 htopZero

end QsOtherFacetPrPairReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
